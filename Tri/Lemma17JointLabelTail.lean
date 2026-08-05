/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17LabelTail

/-!
# The Lemma 17 label tail on the joint path

The stopped reaction-label word can end with a two-activation batch.  Removing
that possible one-identity overshoot costs one unit of adverse label radius.
The resulting bad prefix is a maximal-prefix event for the genuine physical
first-`k` reveal path, so the Lemma 16 urn bound transfers to the joint path.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Dropping at most one final revealed identity costs at most one unit of
adverse label excess. -/
theorem lemma17_word_bad_drop_one
    {n : ℕ} (label : Fin n → InfectionLabel)
    (rho k : ℕ) (word : List (Fin n))
    (hnodup : word.Nodup)
    (hlen : word.length ≤ k + 1)
    (hklen : k < word.length)
    (hbad :
      infectionRevealWordXCount label word + (rho + 1) <
        infectionRevealWordYCount label word) :
    infectionRevealWordXCount label (word.take k) + rho <
      infectionRevealWordYCount label (word.take k) := by
  let pref := word.take k
  let suff := word.drop k
  have hdecomp : pref ++ suff = word :=
    List.take_append_drop k word
  have hparts :
      pref.Nodup ∧ suff.Nodup ∧
        Disjoint pref.toFinset suff.toFinset := by
    have hp :
        pref.Nodup ∧ suff.Nodup ∧
          ∀ a ∈ pref, ∀ b ∈ suff, a ≠ b := by
      apply List.nodup_append.mp
      rw [hdecomp]
      exact hnodup
    refine ⟨hp.1, hp.2.1, ?_⟩
    rw [Finset.disjoint_left]
    intro i hiPref hiSuff
    exact
      (hp.2.2 i (List.mem_toFinset.mp hiPref)
        i (List.mem_toFinset.mp hiSuff)) rfl
  have hX :=
    infectionRevealWordXCount_append_of_disjoint
      label pref suff hparts.2.2
  have hY :=
    infectionRevealWordYCount_append_of_disjoint
      label pref suff hparts.2.2
  have hsuffixLabels :=
    infectionRevealWordXCount_add_YCount
      label suff hparts.2.1
  have hsuffixLength : suff.length ≤ 1 := by
    dsimp only [suff]
    rw [List.length_drop]
    omega
  have hbad' := hbad
  rw [← hdecomp, hX, hY] at hbad'
  change
    infectionRevealWordXCount label pref + rho <
      infectionRevealWordYCount label pref
  omega

/-- A stopped reaction-label failure at radius `rho+1` is visible as a
radius-`rho` maximal failure in the durable physical first-`k` word. -/
theorem lemma17LabelBad_succ_implies_logicalMax
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (k A G rho : ℕ)
    (q : Lemma17CountedPathState n)
    (hinv : Lemma17CountedPathInv s k A G q)
    (hlabelInv : Lemma17ReactionLabelInv A G q)
    (hbad : Lemma17LabelBad (rho + 1) q) :
    Lemma17LogicalMaxLabelBad
      s.inactive.initialLabel rho
      (InfectionRevealPrefixCheckpoint.ofPhysical
        (InfectionRevealFirstKQuotient.ofPath
          k q.counted.path)) := by
  rcases hlabelInv.1 with ⟨suffix, hsuffix⟩
  have hanchor :
      q.counted.path.anchor = s := hinv.1.1
  have hreactionNodup :
      q.reactionRevealed.Nodup := by
    have hparts :
        q.reactionRevealed.Nodup ∧ suffix.Nodup ∧
          ∀ a ∈ q.reactionRevealed,
            ∀ b ∈ suffix, a ≠ b := by
      apply List.nodup_append.mp
      rw [← hsuffix]
      exact q.counted.path.hnodup
    exact hparts.1
  have hreactionLength :
      q.reactionRevealed.length ≤ k + 1 := by
    have hprefix :
        q.reactionRevealed.length ≤
          q.counted.path.revealed.length := by
      rw [hsuffix, List.length_append]
      omega
    exact hprefix.trans hinv.1.2
  have hbadWord :
      infectionRevealWordXCount
            s.inactive.initialLabel
            q.reactionRevealed +
          (rho + 1) <
        infectionRevealWordYCount
          s.inactive.initialLabel
          q.reactionRevealed := by
    unfold Lemma17LabelBad at hbad
    have hX := hlabelInv.2.1
    have hY := hlabelInv.2.2.1
    rw [hanchor] at hX hY
    rw [← hX, ← hY]
    exact hbad
  let j := q.reactionRevealed.length
  have hjPath :
      q.counted.path.revealed.take j =
        q.reactionRevealed := by
    dsimp only [j]
    rw [hsuffix]
    simpa using
      (List.take_append_of_le_length
        (l₂ := suffix)
        (show q.reactionRevealed.length ≤
          q.reactionRevealed.length from le_rfl))
  by_cases hj : j ≤ k
  · have hcheckpointTake :
        (InfectionRevealPrefixCheckpoint.ofPhysical
          (InfectionRevealFirstKQuotient.ofPath
            k q.counted.path)).word.take j =
          q.reactionRevealed := by
      by_cases hreach :
          k ≤ q.counted.path.revealed.length
      · have hjk :
            (q.counted.path.revealed.take k).take j =
              q.counted.path.revealed.take j := by
          rw [List.take_take, min_eq_left hj]
        simp [InfectionRevealFirstKQuotient.ofPath,
          InfectionRevealPrefixCheckpoint.ofPhysical,
          InfectionRevealPrefixCheckpoint.word,
          hreach, hjk, hjPath]
      · simp [InfectionRevealFirstKQuotient.ofPath,
          InfectionRevealPrefixCheckpoint.ofPhysical,
          InfectionRevealPrefixCheckpoint.word,
          hreach, hjPath]
    unfold Lemma17LogicalMaxLabelBad
      lemma17WordPrefixBad
    refine ⟨j, ?_, ?_⟩
    · have hwordLength :
          j ≤
            (InfectionRevealPrefixCheckpoint.ofPhysical
              (InfectionRevealFirstKQuotient.ofPath
                k q.counted.path)).word.length := by
        by_cases hreach :
            k ≤ q.counted.path.revealed.length
        · simp [InfectionRevealFirstKQuotient.ofPath,
            InfectionRevealPrefixCheckpoint.ofPhysical,
            InfectionRevealPrefixCheckpoint.word,
            hreach, hj]
        · simp [InfectionRevealFirstKQuotient.ofPath,
            InfectionRevealPrefixCheckpoint.ofPhysical,
            InfectionRevealPrefixCheckpoint.word,
            hreach]
          have hjp :
              j ≤ q.counted.path.revealed.length := by
            dsimp only [j]
            rw [hsuffix, List.length_append]
            omega
          exact hjp
      exact hwordLength
    · rw [hcheckpointTake]
      have hweaker :
          infectionRevealWordXCount
                s.inactive.initialLabel
                q.reactionRevealed + rho <
            infectionRevealWordYCount
              s.inactive.initialLabel
              q.reactionRevealed := by
        omega
      exact hweaker
  · have hklen : k < q.reactionRevealed.length := by
      simpa [j] using hj
    have hprefixBad :=
      lemma17_word_bad_drop_one
        s.inactive.initialLabel rho k
        q.reactionRevealed hreactionNodup
        hreactionLength hklen hbadWord
    have hreach :
        k ≤ q.counted.path.revealed.length := by
      have :
          q.reactionRevealed.length ≤
            q.counted.path.revealed.length := by
        rw [hsuffix, List.length_append]
        omega
      omega
    have htake :
        q.counted.path.revealed.take k =
          q.reactionRevealed.take k := by
      rw [hsuffix]
      exact List.take_append_of_le_length
        (by omega)
    unfold Lemma17LogicalMaxLabelBad
      lemma17WordPrefixBad
    simp only [InfectionRevealFirstKQuotient.ofPath,
      hreach, if_pos,
      InfectionRevealPrefixCheckpoint.ofPhysical,
      InfectionRevealPrefixCheckpoint.word]
    refine ⟨k, ?_, ?_⟩
    · simpa [List.length_take, min_eq_left hreach]
    rw [List.take_take, min_self, htake]
    exact hprefixBad

/-- Forgetting all counters gives the genuine stopped physical path step. -/
def lemma17CountedPathToPath
    {n : ℕ} (q : Lemma17CountedPathState n) :
    InfectionRevealPhysicalPathState n :=
  q.counted.path

theorem lemma17CountedPathStep_map_path
    (n : ℕ) (h3 : 3 ≤ n) (k A G : ℕ)
    (q : Lemma17CountedPathState n) :
    (lemma17CountedPathStep n h3 k A G q).map
        lemma17CountedPathToPath =
      infectionRevealPhysicalFirstKStep
        n h3 k q.counted.path := by
  calc
    (lemma17CountedPathStep n h3 k A G q).map
        lemma17CountedPathToPath =
      ((lemma17CountedPathStep n h3 k A G q).map
        lemma17CountedPathToLemma16).map
          lemma16CountedPathToPath := by
            rw [PMF.map_comp]
            rfl
    _ =
      (lemma16CountedPathStep n h3 k q.counted).map
        lemma16CountedPathToPath := by
          rw [lemma17CountedPathStep_map_lemma16]
    _ =
      infectionRevealPhysicalFirstKStep
        n h3 k q.counted.path :=
      lemma16CountedPathStep_map_path
        n h3 k q.counted

/-- The Lemma 16 maximal physical prefix tail transfers to the joint path,
with one extra adverse unit reserved for a two-activation overshoot. -/
theorem lemma17CountedPath_label_tail
    (n : ℕ) (h3 : 3 ≤ n)
    (qpar rho a k u nu R B A G T : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + k = A)
    (hqa : qpar * a ≤ rho ^ 2)
    (hnu : nu + 1 = n)
    (hk : k + 1 = a)
    (huk : u + k + 1 = nu)
    (hRB : R + B = nu)
    (hquarter : 4 * a ≤ n)
    (hmajor : R ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk0 : 0 < k) :
    terminalFailureMass
        (iter (lemma17CountedPathStep n h3 k A G) T
          (lemma17CountedPathInitial s))
        (fun z => ¬ Lemma17LabelBad (rho + 1) z)
      ≤ lemma16UrnError qpar := by
  let K := lemma17CountedPathStep n h3 k A G
  let q₀ := lemma17CountedPathInitial s
  let μ := iter K T q₀
  let LabelBad : Lemma17CountedPathState n → Prop :=
    Lemma17LabelBad (rho + 1)
  let PathBad : InfectionRevealPhysicalPathState n → Prop :=
    fun z =>
      Lemma17LogicalMaxLabelBad
        s.inactive.initialLabel rho
        (InfectionRevealPrefixCheckpoint.ofPhysical
          (InfectionRevealFirstKQuotient.ofPath k z))
  let P : Lemma17CountedPathState n → Prop :=
    fun z =>
      Lemma17CountedPathInv s k A G z ∧
        Lemma17ReactionLabelInv A G z
  have hclosed :
      ∀ x, P x → ∀ y, K x y ≠ 0 → P y := by
    intro x hx y hy
    exact
      ⟨lemma17CountedPathStep_inv_closed
          n h3 k A G s hanchorActive x y hx.1 hy,
        lemma17CountedPathStep_labelInv_closed
          n h3 k A G x y hx.2 hy⟩
  have hcontain :
      ∀ z, P z → LabelBad z →
        PathBad (lemma17CountedPathToPath z) := by
    intro z hz hbad
    exact
      lemma17LabelBad_succ_implies_logicalMax
        s k A G rho z hz.1 hz.2 hbad
  have hinitial : P q₀ :=
    ⟨lemma17CountedPathInitial_inv s k A G,
      lemma17CountedPathInitial_labelInv A G s⟩
  have hterminal :
      terminalFailureMass μ (fun z => ¬ LabelBad z) ≤
        hitProb LabelBad K T q₀ :=
    terminalEventMass_iter_le_hitProb
      LabelBad K T q₀
  have hmono :
      hitProb LabelBad K T q₀ ≤
        hitProb
          (fun z =>
            PathBad (lemma17CountedPathToPath z))
          K T q₀ :=
    hitProb_mono_target_of_support_invariant
      K LabelBad
      (fun z =>
        PathBad (lemma17CountedPathToPath z))
      P hclosed hcontain T q₀ hinitial
  have hintertwines :
      Intertwines lemma17CountedPathToPath K
        (infectionRevealPhysicalFirstKStep n h3 k) :=
    lemma17CountedPathStep_map_path n h3 k A G
  have htransfer :
      hitProb
          (fun z =>
            PathBad (lemma17CountedPathToPath z))
          K T q₀ =
        hitProb PathBad
          (infectionRevealPhysicalFirstKStep n h3 k)
          T (infectionRevealPhysicalPathInitial s) := by
    simpa [q₀, lemma17CountedPathInitial,
      lemma17CountedPathToPath,
      lemma16CountedPathInitial] using
      hitProb_transfer hintertwines PathBad T q₀
  have hfinite :
      hitProb PathBad
          (infectionRevealPhysicalFirstKStep n h3 k)
          T (infectionRevealPhysicalPathInitial s) ≤
        everHit PathBad
          (infectionRevealPhysicalFirstKStep n h3 k)
          (infectionRevealPhysicalPathInitial s) := by
    exact le_iSup
      (fun U =>
        hitProb PathBad
          (infectionRevealPhysicalFirstKStep n h3 k)
          U (infectionRevealPhysicalPathInitial s)) T
  have hphysical :
      everHit PathBad
          (infectionRevealPhysicalFirstKStep n h3 k)
          (infectionRevealPhysicalPathInitial s) ≤
        lemma16UrnError qpar := by
    simpa [PathBad] using
      infectionRevealPhysical_lemma17_max_prefix_tail
        n h3 qpar rho a k u nu R B s
        hqa hnu hk huk hRB hquarter hmajor
        hx0 hy0 hk0
  calc
    terminalFailureMass
          (iter (lemma17CountedPathStep n h3 k A G) T
            (lemma17CountedPathInitial s))
          (fun z => ¬ Lemma17LabelBad (rho + 1) z) ≤
        hitProb LabelBad K T q₀ := by
          simpa [μ, K, q₀, LabelBad] using hterminal
    _ ≤
        hitProb
          (fun z =>
            PathBad (lemma17CountedPathToPath z))
          K T q₀ := hmono
    _ =
        hitProb PathBad
          (infectionRevealPhysicalFirstKStep n h3 k)
          T (infectionRevealPhysicalPathInitial s) :=
      htransfer
    _ ≤
        everHit PathBad
          (infectionRevealPhysicalFirstKStep n h3 k)
          (infectionRevealPhysicalPathInitial s) :=
      hfinite
    _ ≤ lemma16UrnError qpar := hphysical

end

end Tri

#print axioms Tri.lemma17_word_bad_drop_one
#print axioms Tri.lemma17LabelBad_succ_implies_logicalMax
#print axioms Tri.lemma17CountedPathStep_map_path
#print axioms Tri.lemma17CountedPath_label_tail
