/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17LabelPath

/-!
# Maximal immutable-label prefix tail for Lemma 17

A bad selected prefix of any length inside a fixed reveal window is embedded
in the same negative-tilt urn event.  The proof distinguishes the historical
maximal-prefix event from the current-prefix event and compares their
first-hitting probabilities.  The resulting one-at-a-time bound transfers to
the genuine zero/one/two-activation physical clock.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- A bad selected prefix of any length `j ≤ k` forces the fixed maximal
negative-tilt urn event whose clock runs through the whole `k`-window. -/
theorem lemma17_selected_prefix_bad_implies_urnWindowBadY
    (rho u k j R B xSel ySel xRem yRem : ℕ)
    (hRB : R + B = u + k + 1)
    (hmajor : R ≤ B)
    (hselected : xSel + ySel = j)
    (hj : j ≤ k)
    (hx : xSel + xRem = B)
    (hy : ySel + yRem = R)
    (hbad : xSel + rho < ySel)
    (hk : 0 < k) :
    Lemma16UrnWindowBadY rho u k R B
      (xRem, yRem) := by
  have hnu : 0 < R + B := by omega
  have hdev :=
    lemma16_newLabelBad_implies_centeredRed
      R B (R + B) j xSel ySel rho
      hnu rfl hmajor hselected hbad
  have hclock : u + 1 ≤ xRem + yRem := by
    omega
  have hremPosR :
      (0 : ℝ) < (xRem : ℝ) + (yRem : ℝ) := by
    have : 0 < xRem + yRem := by omega
    exact_mod_cast this
  have hnuPosR :
      (0 : ℝ) < (R : ℝ) + (B : ℝ) := by
    exact_mod_cast hnu
  have hremLeNu :
      (xRem : ℝ) + (yRem : ℝ) ≤
        (R : ℝ) + (B : ℝ) := by
    exact_mod_cast (show xRem + yRem ≤ R + B by
      omega)
  let num : ℝ :=
    (ySel : ℝ) -
      (j : ℝ) *
        ((R : ℝ) / ((R : ℝ) + (B : ℝ)))
  have hnum :
      (rho : ℝ) / 2 ≤ num := by
    simpa only [Nat.cast_add] using hdev.le
  have hnum0 : 0 ≤ num := by
    exact
      (by positivity :
        (0 : ℝ) ≤ (rho : ℝ) / 2).trans hnum
  have hidentity :
      (xRem : ℝ) /
            ((xRem : ℝ) + (yRem : ℝ)) -
          (B : ℝ) / ((B : ℝ) + (R : ℝ)) =
        num /
          ((xRem : ℝ) + (yRem : ℝ)) := by
    dsimp only [num]
    have hxR :
        (xSel : ℝ) + (xRem : ℝ) = (B : ℝ) := by
      exact_mod_cast hx
    have hyR :
        (ySel : ℝ) + (yRem : ℝ) = (R : ℝ) := by
      exact_mod_cast hy
    have hselR :
        (xSel : ℝ) + (ySel : ℝ) = (j : ℝ) := by
      exact_mod_cast hselected
    rw [add_comm (B : ℝ) (R : ℝ)]
    field_simp [ne_of_gt hremPosR,
      ne_of_gt hnuPosR]
    nlinarith
  have hdelta :
      (rho : ℝ) /
            (2 * ((B : ℝ) + (R : ℝ))) ≤
        (xRem : ℝ) /
            ((xRem : ℝ) + (yRem : ℝ)) -
          (B : ℝ) / ((B : ℝ) + (R : ℝ)) := by
    rw [hidentity]
    have hfirst :
        (rho : ℝ) /
              (2 * ((B : ℝ) + (R : ℝ))) ≤
          num / ((R : ℝ) + (B : ℝ)) := by
      rw [show
          (rho : ℝ) /
              (2 * ((B : ℝ) + (R : ℝ))) =
            ((rho : ℝ) / 2) /
              ((R : ℝ) + (B : ℝ)) by
        rw [add_comm (B : ℝ) (R : ℝ)]
        field_simp [ne_of_gt hnuPosR]]
      exact
        (div_le_div_iff_of_pos_right
          hnuPosR).2 hnum
    exact hfirst.trans
      (div_le_div_of_nonneg_left
        hnum0 hremPosR hremLeNu)
  refine ⟨?_, ?_⟩
  · simpa only [Prod.fst, Prod.snd] using
      hclock
  · let delta : ℝ :=
      (rho : ℝ) /
        (2 * ((B : ℝ) + (R : ℝ)))
    let AA : ℝ :=
      2 * (k : ℝ) /
        (((u : ℝ) + 1) *
          ((B : ℝ) + (R : ℝ)))
    let lam : ℝ := 4 * delta / AA
    have hkPosR : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast hk
    have hBRPosR :
        (0 : ℝ) < (B : ℝ) + (R : ℝ) := by
      nlinarith [hnuPosR]
    have hAA : 0 < AA := by
      dsimp only [AA]
      positivity
    have hdelta0 : 0 ≤ delta := by
      dsimp only [delta]
      positivity
    have hlam0 : 0 ≤ lam := by
      dsimp only [lam]
      positivity
    change
      |-lam| * delta ≤
        (-lam) *
          urnM
            ((B : ℝ) / ((B : ℝ) + (R : ℝ)))
            (xRem, yRem)
    rw [abs_neg, abs_of_nonneg hlam0]
    unfold urnM
    have hM :
        delta ≤
          -((B : ℝ) / ((B : ℝ) + (R : ℝ)) -
            (xRem : ℝ) /
              ((xRem : ℝ) + (yRem : ℝ))) := by
      dsimp only [delta]
      linarith
    nlinarith

/-- The currently revealed one-at-a-time trace prefix has adverse immutable
label excess larger than `rho`. -/
def Lemma17TraceCurrentLabelBad
    {n : ℕ} (rho : ℕ)
    (q : InfectionRevealTraceState n) : Prop :=
  infectionRevealWordXCount
        q.anchor.initialLabel q.revealed + rho <
    infectionRevealWordYCount
      q.anchor.initialLabel q.revealed

noncomputable instance lemma17TraceCurrentLabelBadDecidable
    {n : ℕ} (rho : ℕ) :
    DecidablePred (@Lemma17TraceCurrentLabelBad n rho) :=
  Classical.decPred _

/-- A bad current trace prefix inside the first `k` reveals is contained in
the fixed maximal urn event. -/
theorem lemma17_traceCurrentBad_implies_urnWindowBadY
    {n : ℕ} (v : InfectionInactiveView n)
    (rho u k R B : ℕ)
    (hRB : R + B = u + k + 1)
    (hmajor : R ≤ B)
    (hx0 : v.xIds.card = B)
    (hy0 : v.yIds.card = R)
    (hk : 0 < k)
    (q : InfectionRevealTraceState n)
    (hq : Lemma16TracePrefixInv v k q)
    (hbad : Lemma17TraceCurrentLabelBad rho q) :
    Lemma16UrnWindowBadY rho u k R B
      (infectionRevealTraceCounts q) := by
  let j := q.revealed.length
  have hselected :
      q.revealedXIds.card +
          q.revealedYIds.card = j := by
    dsimp only [j]
    simpa using
      infectionRevealWordXCount_add_YCount
        q.anchor.initialLabel q.revealed q.hnodup
  have hj : j ≤ k := hq.2
  have hxLedger :
      q.revealedXIds.card +
          q.current.xIds.card = B := by
    calc
      q.revealedXIds.card +
            q.current.xIds.card =
          q.anchor.xIds.card :=
        q.revealedX_card_add_current
      _ = v.xIds.card := by rw [hq.1]
      _ = B := hx0
  have hyLedger :
      q.revealedYIds.card +
          q.current.yIds.card = R := by
    calc
      q.revealedYIds.card +
            q.current.yIds.card =
          q.anchor.yIds.card :=
        q.revealedY_card_add_current
      _ = v.yIds.card := by rw [hq.1]
      _ = R := hy0
  have hbad' :
      q.revealedXIds.card + rho <
        q.revealedYIds.card := by
    simpa [Lemma17TraceCurrentLabelBad] using hbad
  exact
    lemma17_selected_prefix_bad_implies_urnWindowBadY
      rho u k j R B
      q.revealedXIds.card q.revealedYIds.card
      q.current.xIds.card q.current.yIds.card
      hRB hmajor hselected hj hxLedger hyLedger
      hbad' hk

/-- Eventual current-prefix failure on the stopped one-at-a-time trace is
bounded by the maximal urn event. -/
theorem lemma17_trace_current_prefix_everHit_le_urn
    {n : ℕ} (v : InfectionInactiveView n)
    (rho u k R B : ℕ)
    (hRB : R + B = u + k + 1)
    (hmajor : R ≤ B)
    (hx0 : v.xIds.card = B)
    (hy0 : v.yIds.card = R)
    (hk : 0 < k)
    (hroom : k + 2 ≤ v.ids.card) :
    everHit
        (Lemma17TraceCurrentLabelBad rho)
        (infectionRevealTraceFirstKStep k)
        (infectionRevealTraceInitial v)
      ≤
    everHit
        (Lemma16UrnWindowBadY rho u k R B)
        urnStopped (B, R) := by
  let Bad := Lemma16UrnWindowBadY rho u k R B
  let K := @infectionRevealTraceFirstKStep n k
  let P := Lemma16TracePrefixInv v k
  let V : InfectionRevealTraceState n → ℝ≥0∞ :=
    fun z => everHit Bad urnStopped
      (infectionRevealTraceCounts z)
  have hclosed :
      ∀ s, P s → ∀ z, K s z ≠ 0 → P z := by
    intro s hs z hz
    exact
      infectionRevealTraceFirstKStep_prefixInv_closed
        v k s z hs hz
  have hsuper :
      ∀ s, P s → expect (K s) V ≤ V s := by
    intro s hs
    exact
      expect_infectionRevealTraceFirstKStep_urnEverHit_le
        v k hroom Bad s hs
  have hcontain :
      ∀ z, P z → Lemma17TraceCurrentLabelBad rho z →
        (1 : ℝ≥0∞) ≤ V z := by
    intro z hzP hz
    have hurn :=
      lemma17_traceCurrentBad_implies_urnWindowBadY
        v rho u k R B hRB hmajor hx0 hy0 hk
        z hzP hz
    rw [show V z = 1 by
      exact everHit_eq_one_of_mem
        Bad urnStopped
        (infectionRevealTraceCounts z) hurn]
  have hinitial :
      P (infectionRevealTraceInitial v) :=
    ⟨rfl, by simp [infectionRevealTraceInitial]⟩
  have h :=
    ville_frozen_of_support_invariant
      K (Lemma17TraceCurrentLabelBad rho)
      P V 1 (by simp) (by simp)
      hcontain hclosed hsuper
      (infectionRevealTraceInitial v) hinitial
  have hcounts :
      infectionRevealTraceCounts
          (infectionRevealTraceInitial v) =
        (B, R) := by
    simp [infectionRevealTraceCounts,
      infectionRevealTraceInitial,
      infectionInactiveCounts, hx0, hy0]
  unfold everHit at h ⊢
  dsimp only [V] at h
  rw [hcounts] at h
  simpa [K, P, Bad] using h

/-- The reveal word retained by a logical first-prefix checkpoint. -/
def InfectionRevealPrefixCheckpoint.word
    {n : ℕ} :
    InfectionRevealPrefixCheckpoint n → List (Fin n)
  | .live _ word => word
  | .done word => word

/-- The current logical word has adverse immutable-label excess larger than
`rho`. -/
def Lemma17LogicalCurrentLabelBad
    {n : ℕ} (label : Fin n → InfectionLabel)
    (rho : ℕ)
    (q : InfectionRevealPrefixCheckpoint n) : Prop :=
  infectionRevealWordXCount label q.word + rho <
    infectionRevealWordYCount label q.word

noncomputable instance lemma17LogicalCurrentLabelBadDecidable
    {n : ℕ} (label : Fin n → InfectionLabel)
    (rho : ℕ) :
    DecidablePred
      (Lemma17LogicalCurrentLabelBad label rho) :=
  Classical.decPred _

/-- On the reachable stopped-trace invariant, logical current-word failure is
the trace's current-prefix failure. -/
theorem lemma17_logicalCurrentBad_implies_traceCurrentBad
    {n : ℕ} (v : InfectionInactiveView n)
    (rho k : ℕ)
    (q : InfectionRevealTraceState n)
    (hq : Lemma16TracePrefixInv v k q)
    (hbad :
      Lemma17LogicalCurrentLabelBad
        v.initialLabel rho
        (InfectionRevealPrefixCheckpoint.ofTrace k q)) :
    Lemma17TraceCurrentLabelBad rho q := by
  have hanchor : q.anchor = v := hq.1
  have hle : q.revealed.length ≤ k := hq.2
  by_cases hreach : k ≤ q.revealed.length
  · have hlen : q.revealed.length = k := by
      omega
    have htake :
        q.revealed.take k = q.revealed := by
      rw [← hlen, List.take_length]
    simpa [Lemma17LogicalCurrentLabelBad,
      Lemma17TraceCurrentLabelBad,
      InfectionRevealPrefixCheckpoint.word,
      InfectionRevealPrefixCheckpoint.ofTrace,
      hreach, htake, hanchor] using hbad
  · simpa [Lemma17LogicalCurrentLabelBad,
      Lemma17TraceCurrentLabelBad,
      InfectionRevealPrefixCheckpoint.word,
      InfectionRevealPrefixCheckpoint.ofTrace,
      hreach, hanchor] using hbad

/-- The logical stopped one-at-a-time current-prefix event inherits the urn
tail through the anchored reveal trace. -/
theorem lemma17_logical_current_prefix_everHit_le_urn
    {n : ℕ} (v : InfectionInactiveView n)
    (rho u k R B : ℕ)
    (hRB : R + B = u + k + 1)
    (hmajor : R ≤ B)
    (hx0 : v.xIds.card = B)
    (hy0 : v.yIds.card = R)
    (hk : 0 < k)
    (hroom : k + 2 ≤ v.ids.card) :
    everHit
        (Lemma17LogicalCurrentLabelBad
          v.initialLabel rho)
        (InfectionRevealPrefixCheckpoint.oneStep n k)
        (.live v [])
      ≤
    everHit
        (Lemma16UrnWindowBadY rho u k R B)
        urnStopped (B, R) := by
  let Bad := Lemma16UrnWindowBadY rho u k R B
  let K := @infectionRevealTraceFirstKStep n k
  let P := Lemma16TracePrefixInv v k
  let V : InfectionRevealTraceState n → ℝ≥0∞ :=
    fun z => everHit Bad urnStopped
      (infectionRevealTraceCounts z)
  let Target : InfectionRevealTraceState n → Prop :=
    fun z =>
      Lemma17LogicalCurrentLabelBad
        v.initialLabel rho
        (InfectionRevealPrefixCheckpoint.ofTrace k z)
  have hclosed :
      ∀ s, P s → ∀ z, K s z ≠ 0 → P z := by
    intro s hs z hz
    exact
      infectionRevealTraceFirstKStep_prefixInv_closed
        v k s z hs hz
  have hsuper :
      ∀ s, P s → expect (K s) V ≤ V s := by
    intro s hs
    exact
      expect_infectionRevealTraceFirstKStep_urnEverHit_le
        v k hroom Bad s hs
  have hcontain :
      ∀ z, P z → Target z →
        (1 : ℝ≥0∞) ≤ V z := by
    intro z hzP hz
    have hcurrent :=
      lemma17_logicalCurrentBad_implies_traceCurrentBad
        v rho k z hzP hz
    have hurn :=
      lemma17_traceCurrentBad_implies_urnWindowBadY
        v rho u k R B hRB hmajor hx0 hy0 hk
        z hzP hcurrent
    rw [show V z = 1 by
      exact everHit_eq_one_of_mem
        Bad urnStopped
        (infectionRevealTraceCounts z) hurn]
  have hinitial :
      P (infectionRevealTraceInitial v) :=
    ⟨rfl, by simp [infectionRevealTraceInitial]⟩
  have h :=
    ville_frozen_of_support_invariant
      K Target P V 1 (by simp) (by simp)
      hcontain hclosed hsuper
      (infectionRevealTraceInitial v) hinitial
  have hcounts :
      infectionRevealTraceCounts
          (infectionRevealTraceInitial v) =
        (B, R) := by
    simp [infectionRevealTraceCounts,
      infectionRevealTraceInitial,
      infectionInactiveCounts, hx0, hy0]
  have hkne : k ≠ 0 := by omega
  have htransfer :
      everHit Target K
          (infectionRevealTraceInitial v) =
        everHit
          (Lemma17LogicalCurrentLabelBad
            v.initialLabel rho)
          (InfectionRevealPrefixCheckpoint.oneStep n k)
          (.live v []) := by
    unfold everHit
    simpa [Target, K, infectionRevealTraceInitial,
      InfectionRevealPrefixCheckpoint.ofTrace,
      hkne] using
      iSup_hitProb_transfer
        (infectionRevealTraceFirstKStep_intertwines_checkpoint
          n k)
        (Lemma17LogicalCurrentLabelBad
          v.initialLabel rho)
        (infectionRevealTraceInitial v)
  rw [← htransfer]
  unfold everHit at h ⊢
  dsimp only [V] at h
  rw [hcounts] at h
  simpa [K, P, Bad, Target] using h

/-- Some prefix of a word has adverse immutable-label excess larger than
`rho`. -/
def lemma17WordPrefixBad
    {n : ℕ} (label : Fin n → InfectionLabel)
    (rho : ℕ) (word : List (Fin n)) : Prop :=
  ∃ j, j ≤ word.length ∧
    infectionRevealWordXCount label (word.take j) + rho <
      infectionRevealWordYCount label (word.take j)

noncomputable instance lemma17WordPrefixBadDecidable
    {n : ℕ} (label : Fin n → InfectionLabel)
    (rho : ℕ) :
    DecidablePred (lemma17WordPrefixBad label rho) :=
  Classical.decPred _

/-- A current-word failure is one of the word's prefix failures. -/
theorem lemma17_currentLabelBad_implies_wordPrefixBad
    {n : ℕ} (label : Fin n → InfectionLabel)
    (rho : ℕ) (word : List (Fin n))
    (hbad :
      infectionRevealWordXCount label word + rho <
        infectionRevealWordYCount label word) :
    lemma17WordPrefixBad label rho word := by
  refine ⟨word.length, le_rfl, ?_⟩
  simpa using hbad

/-- If appending one identity creates a prefix failure when none existed
before, the whole new word is currently bad. -/
theorem lemma17_current_bad_of_prefix_bad_append_singleton
    {n : ℕ} (label : Fin n → InfectionLabel)
    (rho : ℕ) (word : List (Fin n)) (i : Fin n)
    (hgood : ¬ lemma17WordPrefixBad label rho word)
    (hbad :
      lemma17WordPrefixBad label rho (word ++ [i])) :
    infectionRevealWordXCount label (word ++ [i]) + rho <
      infectionRevealWordYCount label (word ++ [i]) := by
  rcases hbad with ⟨j, hj, hjbad⟩
  by_cases hjo : j ≤ word.length
  · apply False.elim
    apply hgood
    refine ⟨j, hjo, ?_⟩
    have htake :
        (word ++ [i]).take j = word.take j :=
      List.take_append_of_le_length hjo
    simpa [htake] using hjbad
  · have hjlen :
        j = (word ++ [i]).length := by
      simp only [List.length_append, List.length_cons,
        List.length_nil] at hj
      simp only [List.length_append, List.length_cons,
        List.length_nil]
      omega
    rw [hjlen, List.take_length] at hjbad
    exact hjbad

/-- Some prefix of the stopped one-at-a-time trace is bad. -/
def Lemma17TraceMaxLabelBad
    {n : ℕ} (rho : ℕ)
    (q : InfectionRevealTraceState n) : Prop :=
  lemma17WordPrefixBad
    q.anchor.initialLabel rho q.revealed

noncomputable instance lemma17TraceMaxLabelBadDecidable
    {n : ℕ} (rho : ℕ) :
    DecidablePred (@Lemma17TraceMaxLabelBad n rho) :=
  Classical.decPred _

/-- A current trace failure is a maximal-prefix failure. -/
theorem lemma17_traceCurrentBad_implies_maxBad
    {n : ℕ} (rho : ℕ)
    (q : InfectionRevealTraceState n)
    (hbad : Lemma17TraceCurrentLabelBad rho q) :
    Lemma17TraceMaxLabelBad rho q := by
  exact
    lemma17_currentLabelBad_implies_wordPrefixBad
      q.anchor.initialLabel rho q.revealed hbad

/-- From a trace with no previous prefix failure, a supported step that
enters the maximal bad set is currently bad. -/
theorem lemma17_traceStep_entry_max_is_current
    {n : ℕ} (rho k : ℕ)
    (q z : InfectionRevealTraceState n)
    (hq : ¬ Lemma17TraceMaxLabelBad rho q)
    (hz :
      infectionRevealTraceFirstKStep k q z ≠ 0)
    (hzbad : Lemma17TraceMaxLabelBad rho z) :
    Lemma17TraceCurrentLabelBad rho z := by
  by_cases hreach : InfectionRevealTraceReached k q
  · have hzq : z = q := by
      unfold infectionRevealTraceFirstKStep at hz
      rw [freeze_of_mem q hreach] at hz
      by_contra hne
      simp [PMF.pure_apply, hne] at hz
    exact False.elim (hq (by simpa [hzq] using hzbad))
  · unfold infectionRevealTraceFirstKStep at hz
    rw [freeze_of_not_mem q hreach] at hz
    unfold infectionRevealTraceStep at hz
    by_cases hcard : 0 < q.current.ids.card
    · rw [dif_pos hcard] at hz
      have hzmem :
          z ∈
            ((infectionRevealOnePMF q.current
              (infectionRevealOne_nonempty_of_card_pos
                q.current hcard)).map q.afterOne).support :=
        hz
      rw [PMF.support_map] at hzmem
      rcases hzmem with ⟨i, hi, rfl⟩
      unfold Lemma17TraceCurrentLabelBad
      exact
        lemma17_current_bad_of_prefix_bad_append_singleton
          q.anchor.initialLabel rho q.revealed i.1
          hq hzbad
    · rw [dif_neg hcard] at hz
      have hzq : z = q := by
        by_contra hne
        simp [PMF.pure_apply, hne] at hz
      exact False.elim (hq (by simpa [hzq] using hzbad))

/-- First hitting the historical maximal-prefix event is no more likely than
first hitting the current-prefix event. -/
theorem lemma17_trace_max_hitProb_le_current
    {n : ℕ} (rho k : ℕ) :
    ∀ (T : ℕ) (q : InfectionRevealTraceState n),
      ¬ Lemma17TraceMaxLabelBad rho q →
      hitProb
          (Lemma17TraceMaxLabelBad rho)
          (infectionRevealTraceFirstKStep k) T q
        ≤
      hitProb
          (Lemma17TraceCurrentLabelBad rho)
          (infectionRevealTraceFirstKStep k) T q := by
  intro T
  induction T with
  | zero =>
      intro q hq
      have hcurrent :
          ¬ Lemma17TraceCurrentLabelBad rho q := by
        intro hbad
        exact hq
          (lemma17_traceCurrentBad_implies_maxBad
            rho q hbad)
      unfold hitProb
      simp [iter, ind, hq, hcurrent]
  | succ T ih =>
      intro q hq
      have hcurrent :
          ¬ Lemma17TraceCurrentLabelBad rho q := by
        intro hbad
        exact hq
          (lemma17_traceCurrentBad_implies_maxBad
            rho q hbad)
      rw [hitProb_succ_of_not
          (Lemma17TraceMaxLabelBad rho)
          (infectionRevealTraceFirstKStep k)
          T q hq,
        hitProb_succ_of_not
          (Lemma17TraceCurrentLabelBad rho)
          (infectionRevealTraceFirstKStep k)
          T q hcurrent]
      exact ENNReal.tsum_le_tsum fun z => by
        by_cases hz :
            infectionRevealTraceFirstKStep k q z = 0
        · simp [hz]
        · apply mul_le_mul_left'
          by_cases hzbad :
              Lemma17TraceMaxLabelBad rho z
          · have hzcurrent :=
              lemma17_traceStep_entry_max_is_current
                rho k q z hq hz hzbad
            rw [hitProb_eq_one_of_mem
                (Lemma17TraceMaxLabelBad rho)
                (infectionRevealTraceFirstKStep k)
                T z hzbad,
              hitProb_eq_one_of_mem
                (Lemma17TraceCurrentLabelBad rho)
                (infectionRevealTraceFirstKStep k)
                T z hzcurrent]
          · exact ih z hzbad

/-- Eventual maximal-prefix failure on the one-at-a-time trace is bounded by
eventual current-prefix failure. -/
theorem lemma17_trace_max_everHit_le_current
    {n : ℕ} (rho k : ℕ)
    (q : InfectionRevealTraceState n)
    (hq : ¬ Lemma17TraceMaxLabelBad rho q) :
    everHit
        (Lemma17TraceMaxLabelBad rho)
        (infectionRevealTraceFirstKStep k) q
      ≤
    everHit
        (Lemma17TraceCurrentLabelBad rho)
        (infectionRevealTraceFirstKStep k) q := by
  unfold everHit
  exact iSup_mono fun T =>
    lemma17_trace_max_hitProb_le_current
      rho k T q hq

/-- Some prefix of the word retained by a logical checkpoint is bad. -/
def Lemma17LogicalMaxLabelBad
    {n : ℕ} (label : Fin n → InfectionLabel)
    (rho : ℕ)
    (q : InfectionRevealPrefixCheckpoint n) : Prop :=
  lemma17WordPrefixBad label rho q.word

noncomputable instance lemma17LogicalMaxLabelBadDecidable
    {n : ℕ} (label : Fin n → InfectionLabel)
    (rho : ℕ) :
    DecidablePred
      (Lemma17LogicalMaxLabelBad label rho) :=
  Classical.decPred _

/-- Target monotonicity when containment is available only on a support
invariant. -/
theorem hitProb_mono_target_of_support_invariant
    {α : Type*}
    (K : α → PMF α)
    (B C P : α → Prop)
    [DecidablePred B] [DecidablePred C]
    (hclosed :
      ∀ x, P x → ∀ y, K x y ≠ 0 → P y)
    (hBC : ∀ x, P x → B x → C x) :
    ∀ (T : ℕ) (x : α), P x →
      hitProb B K T x ≤ hitProb C K T x := by
  intro T
  induction T with
  | zero =>
      intro x hx
      by_cases hC : C x
      · rw [hitProb_eq_one_of_mem C K 0 x hC]
        exact hitProb_le_one B K 0 x
      · have hB : ¬ B x := fun hBx =>
          hC (hBC x hx hBx)
        unfold hitProb
        simp [iter, ind, hB, hC]
  | succ T ih =>
      intro x hx
      by_cases hC : C x
      · rw [hitProb_eq_one_of_mem C K (T + 1) x hC]
        exact hitProb_le_one B K (T + 1) x
      · have hB : ¬ B x := fun hBx =>
          hC (hBC x hx hBx)
        rw [hitProb_succ_of_not B K T x hB,
          hitProb_succ_of_not C K T x hC]
        exact ENNReal.tsum_le_tsum fun y => by
          by_cases hy : K x y = 0
          · simp [hy]
          · exact mul_le_mul_left'
              (ih y (hclosed x hx y hy)) _

/-- Eventual target monotonicity under a support invariant. -/
theorem everHit_mono_target_of_support_invariant
    {α : Type*}
    (K : α → PMF α)
    (B C P : α → Prop)
    [DecidablePred B] [DecidablePred C]
    (hclosed :
      ∀ x, P x → ∀ y, K x y ≠ 0 → P y)
    (hBC : ∀ x, P x → B x → C x)
    (x : α) (hx : P x) :
    everHit B K x ≤ everHit C K x := by
  unfold everHit
  exact iSup_mono fun T =>
    hitProb_mono_target_of_support_invariant
      K B C P hclosed hBC T x hx

/-- On the stopped trace invariant, a logical quotient prefix failure is a
genuine trace prefix failure. -/
theorem lemma17_logicalMaxBad_implies_traceMaxBad
    {n : ℕ} (v : InfectionInactiveView n)
    (rho k : ℕ)
    (q : InfectionRevealTraceState n)
    (hq : Lemma16TracePrefixInv v k q)
    (hbad :
      Lemma17LogicalMaxLabelBad
        v.initialLabel rho
        (InfectionRevealPrefixCheckpoint.ofTrace k q)) :
    Lemma17TraceMaxLabelBad rho q := by
  have hanchor : q.anchor = v := hq.1
  have hle : q.revealed.length ≤ k := hq.2
  by_cases hreach : k ≤ q.revealed.length
  · have hlen : q.revealed.length = k := by
      omega
    have htake :
        q.revealed.take k = q.revealed := by
      rw [← hlen, List.take_length]
    simpa [Lemma17LogicalMaxLabelBad,
      Lemma17TraceMaxLabelBad,
      InfectionRevealPrefixCheckpoint.word,
      InfectionRevealPrefixCheckpoint.ofTrace,
      hreach, htake, hanchor] using hbad
  · simpa [Lemma17LogicalMaxLabelBad,
      Lemma17TraceMaxLabelBad,
      InfectionRevealPrefixCheckpoint.word,
      InfectionRevealPrefixCheckpoint.ofTrace,
      hreach, hanchor] using hbad

/-- Logical maximal-prefix failure inherits the maximal urn tail. -/
theorem lemma17_logical_max_prefix_everHit_le_urn
    {n : ℕ} (v : InfectionInactiveView n)
    (rho u k R B : ℕ)
    (hRB : R + B = u + k + 1)
    (hmajor : R ≤ B)
    (hx0 : v.xIds.card = B)
    (hy0 : v.yIds.card = R)
    (hk : 0 < k)
    (hroom : k + 2 ≤ v.ids.card) :
    everHit
        (Lemma17LogicalMaxLabelBad
          v.initialLabel rho)
        (InfectionRevealPrefixCheckpoint.oneStep n k)
        (.live v [])
      ≤
    everHit
        (Lemma16UrnWindowBadY rho u k R B)
        urnStopped (B, R) := by
  let K := @infectionRevealTraceFirstKStep n k
  let P := Lemma16TracePrefixInv v k
  let QuotientBad : InfectionRevealTraceState n → Prop :=
    fun z =>
      Lemma17LogicalMaxLabelBad
        v.initialLabel rho
        (InfectionRevealPrefixCheckpoint.ofTrace k z)
  have hclosed :
      ∀ x, P x → ∀ y, K x y ≠ 0 → P y := by
    intro x hx y hy
    exact
      infectionRevealTraceFirstKStep_prefixInv_closed
        v k x y hx hy
  have hmono :
      everHit QuotientBad K
          (infectionRevealTraceInitial v) ≤
        everHit
          (Lemma17TraceMaxLabelBad rho) K
          (infectionRevealTraceInitial v) := by
    apply
      everHit_mono_target_of_support_invariant
        K QuotientBad
        (Lemma17TraceMaxLabelBad rho) P
        hclosed
    · intro z hzP hz
      exact
        lemma17_logicalMaxBad_implies_traceMaxBad
          v rho k z hzP hz
    · exact
        ⟨rfl, by
          simp [infectionRevealTraceInitial]⟩
  have hmaxCurrent :
      everHit
          (Lemma17TraceMaxLabelBad rho) K
          (infectionRevealTraceInitial v) ≤
        everHit
          (Lemma17TraceCurrentLabelBad rho) K
          (infectionRevealTraceInitial v) := by
    apply lemma17_trace_max_everHit_le_current
    simp [Lemma17TraceMaxLabelBad,
      lemma17WordPrefixBad,
      infectionRevealTraceInitial,
      infectionRevealWordXCount,
      infectionRevealWordYCount]
  have hcurrent :=
    lemma17_trace_current_prefix_everHit_le_urn
      v rho u k R B hRB hmajor hx0 hy0 hk hroom
  have hkne : k ≠ 0 := by omega
  have htransfer :
      everHit QuotientBad K
          (infectionRevealTraceInitial v) =
        everHit
          (Lemma17LogicalMaxLabelBad
            v.initialLabel rho)
          (InfectionRevealPrefixCheckpoint.oneStep n k)
          (.live v []) := by
    unfold everHit
    simpa [QuotientBad, K,
      infectionRevealTraceInitial,
      InfectionRevealPrefixCheckpoint.ofTrace,
      hkne] using
      iSup_hitProb_transfer
        (infectionRevealTraceFirstKStep_intertwines_checkpoint
          n k)
        (Lemma17LogicalMaxLabelBad
          v.initialLabel rho)
        (infectionRevealTraceInitial v)
  rw [← htransfer]
  exact hmono.trans (hmaxCurrent.trans hcurrent)

/-- Genuine physical activation batches satisfy the maximal immutable-label
prefix tail through their first `k` revealed identities. -/
theorem infectionRevealPhysical_lemma17_max_prefix_tail
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
        (fun z =>
          Lemma17LogicalMaxLabelBad
            s.inactive.initialLabel rho
            (InfectionRevealPrefixCheckpoint.ofPhysical
              (InfectionRevealFirstKQuotient.ofPath k z)))
        (infectionRevealPhysicalFirstKStep n h3 k)
        (infectionRevealPhysicalPathInitial s)
      ≤ lemma16UrnError q := by
  have hsum : R + B = u + k + 1 := by omega
  have hidscard :
      s.inactive.ids.card = R + B := by
    calc
      s.inactive.ids.card =
          s.inactive.xIds.card +
            s.inactive.yIds.card := by
        rw [
          InfectionInactiveView.xIds_card_add_yIds_card]
      _ = R + B := by omega
  have hroom : k + 2 ≤ s.inactive.ids.card := by
    omega
  calc
    everHit
        (fun z =>
          Lemma17LogicalMaxLabelBad
            s.inactive.initialLabel rho
            (InfectionRevealPrefixCheckpoint.ofPhysical
              (InfectionRevealFirstKQuotient.ofPath k z)))
        (infectionRevealPhysicalFirstKStep n h3 k)
        (infectionRevealPhysicalPathInitial s)
        ≤
      everHit
        (Lemma17LogicalMaxLabelBad
          s.inactive.initialLabel rho)
        (InfectionRevealPrefixCheckpoint.oneStep n k)
        (.live s.inactive []) :=
      infectionRevealPhysicalFirstK_initial_everHit_le_logical
        n h3 k s hk0 hroom
          (Lemma17LogicalMaxLabelBad
            s.inactive.initialLabel rho)
    _ ≤
      everHit
        (Lemma16UrnWindowBadY rho u k R B)
        urnStopped (B, R) :=
      lemma17_logical_max_prefix_everHit_le_urn
        s.inactive rho u k R B hsum hmajor
        hx0 hy0 hk0 hroom
    _ ≤ lemma16UrnError q := by
      unfold everHit
      exact
        lemma16_urn_window_tail_Y
          q rho n a k u nu R B
          hqa hnu hk huk hRB hquarter hk0

end

end Tri

#print axioms Tri.lemma17_selected_prefix_bad_implies_urnWindowBadY
#print axioms Tri.lemma17_traceCurrentBad_implies_urnWindowBadY
#print axioms Tri.lemma17_trace_current_prefix_everHit_le_urn
#print axioms Tri.lemma17_traceStep_entry_max_is_current
#print axioms Tri.lemma17_trace_max_hitProb_le_current
#print axioms Tri.hitProb_mono_target_of_support_invariant
#print axioms Tri.lemma17_logical_max_prefix_everHit_le_urn
#print axioms Tri.infectionRevealPhysical_lemma17_max_prefix_tail
