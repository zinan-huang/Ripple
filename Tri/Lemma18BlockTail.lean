/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma18StageAssembly
import Tri.Lemma17PoolTail

/-!
# The strongly biased activation block in Lemma 18

The inactive pool at the decisive stage has a large deterministic `X` gap.
If a fixed-size sample fails to retain the required positive gap, its
remaining pool has made a negative-tilt urn excursion.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- A sample whose positive `X` gap falls below `E` forces the same
negative-tilt urn event used in Lemma 16, provided the initial pool gap puts
its mean at least `rho` beyond `E`. -/
theorem lemma18_selected_gap_bad_implies_urnWindowBadY
    (rho E Gap u k R B xSel ySel xRem yRem : ℕ)
    (hRB : R + B = u + k + 1)
    (hgap : R + Gap ≤ B)
    (hmean : (E + rho) * (R + B) ≤ k * Gap)
    (hselected : xSel + ySel = k)
    (hx : xSel + xRem = B)
    (hy : ySel + yRem = R)
    (hbad : xSel < ySel + E)
    (hk : 0 < k) :
    Lemma16UrnWindowBadY rho u k R B (xRem, yRem) := by
  have hnu : 0 < R + B := by omega
  have hpop : 2 * R + Gap ≤ R + B := by omega
  have hsample : k ≤ 2 * ySel + E := by omega
  have hnuR : (0 : ℝ) < (R : ℝ) + (B : ℝ) := by
    exact_mod_cast hnu
  have hpopR :
      2 * (R : ℝ) + (Gap : ℝ) ≤
        (R : ℝ) + (B : ℝ) := by
    exact_mod_cast hpop
  have hsampleR :
      (k : ℝ) ≤ 2 * (ySel : ℝ) + (E : ℝ) := by
    exact_mod_cast hsample
  have hmeanR :
      ((E : ℝ) + (rho : ℝ)) *
          ((R : ℝ) + (B : ℝ)) ≤
        (k : ℝ) * (Gap : ℝ) := by
    exact_mod_cast hmean
  have hkR : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hpopScaled :
      (k : ℝ) *
          (2 * (R : ℝ) + (Gap : ℝ)) ≤
        (k : ℝ) * ((R : ℝ) + (B : ℝ)) :=
    mul_le_mul_of_nonneg_left hpopR hkR
  have hsampleScaled :
      (k : ℝ) * ((R : ℝ) + (B : ℝ)) ≤
        (2 * (ySel : ℝ) + (E : ℝ)) *
          ((R : ℝ) + (B : ℝ)) :=
    mul_le_mul_of_nonneg_right hsampleR hnuR.le
  have hcenteredNumerator :
      (rho : ℝ) * ((R : ℝ) + (B : ℝ)) ≤
        2 * (ySel : ℝ) * ((R : ℝ) + (B : ℝ)) -
          2 * (k : ℝ) * (R : ℝ) := by
    nlinarith
  have hdev :
      (rho : ℝ) / 2 ≤
        (ySel : ℝ) -
          (k : ℝ) *
            ((R : ℝ) / ((R : ℝ) + (B : ℝ))) := by
    field_simp [ne_of_gt hnuR]
    nlinarith
  have hrem : xRem + yRem = u + 1 := by omega
  have hremPosR :
      (0 : ℝ) < (xRem : ℝ) + (yRem : ℝ) := by
    have : 0 < xRem + yRem := by omega
    exact_mod_cast this
  have hremLeNu :
      (xRem : ℝ) + (yRem : ℝ) ≤
        (R : ℝ) + (B : ℝ) := by
    exact_mod_cast (show xRem + yRem ≤ R + B by omega)
  let num : ℝ :=
    (ySel : ℝ) -
      (k : ℝ) * ((R : ℝ) / ((R : ℝ) + (B : ℝ)))
  have hnum :
      (rho : ℝ) / 2 ≤ num := by
    simpa only using hdev
  have hnum0 : 0 ≤ num := by
    exact (by positivity : (0 : ℝ) ≤ (rho : ℝ) / 2).trans hnum
  have hidentity :
      (xRem : ℝ) /
            ((xRem : ℝ) + (yRem : ℝ)) -
          (B : ℝ) / ((B : ℝ) + (R : ℝ)) =
        num / ((xRem : ℝ) + (yRem : ℝ)) := by
    dsimp only [num]
    have hxR :
        (xSel : ℝ) + (xRem : ℝ) = (B : ℝ) := by
      exact_mod_cast hx
    have hyR :
        (ySel : ℝ) + (yRem : ℝ) = (R : ℝ) := by
      exact_mod_cast hy
    have hselR :
        (xSel : ℝ) + (ySel : ℝ) = (k : ℝ) := by
      exact_mod_cast hselected
    rw [add_comm (B : ℝ) (R : ℝ)]
    field_simp [ne_of_gt hremPosR, ne_of_gt hnuR]
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
        field_simp [ne_of_gt hnuR]]
      exact
        (div_le_div_iff_of_pos_right hnuR).2 hnum
    exact hfirst.trans
      (div_le_div_of_nonneg_left
        hnum0 hremPosR hremLeNu)
  refine ⟨?_, ?_⟩
  · simpa only [Prod.fst, Prod.snd] using
      (show u + 1 ≤ xRem + yRem by omega)
  · let delta : ℝ :=
      (rho : ℝ) / (2 * ((B : ℝ) + (R : ℝ)))
    let A : ℝ :=
      2 * (k : ℝ) /
        (((u : ℝ) + 1) * ((B : ℝ) + (R : ℝ)))
    let lam : ℝ := 4 * delta / A
    have hkPosR : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast hk
    have hBRPosR :
        (0 : ℝ) < (B : ℝ) + (R : ℝ) := by
      nlinarith [hnuR]
    have hA : 0 < A := by
      dsimp only [A]
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

/-- A completed logical activation block has positive `X` gap below `E`. -/
def Lemma18LogicalEndBlockBad
    {n : ℕ} (label : Fin n → InfectionLabel)
    (E : ℕ) :
    InfectionRevealPrefixCheckpoint n → Prop
  | .live _ _ => False
  | .done word =>
      infectionRevealWordXCount label word <
        infectionRevealWordYCount label word + E

noncomputable instance lemma18LogicalEndBlockBadDecidable
    {n : ℕ} (label : Fin n → InfectionLabel)
    (E : ℕ) :
    DecidablePred (Lemma18LogicalEndBlockBad label E) :=
  Classical.decPred _

/-- On a valid stopped trace, a bad completed block is contained in the
negative-tilt urn event for the remaining pool. -/
theorem lemma18_traceLogicalEndBad_implies_urnWindowBadY
    {n : ℕ} (v : InfectionInactiveView n)
    (rho E Gap u k R B : ℕ)
    (hRB : R + B = u + k + 1)
    (hgap : R + Gap ≤ B)
    (hmean : (E + rho) * (R + B) ≤ k * Gap)
    (hx0 : v.xIds.card = B)
    (hy0 : v.yIds.card = R)
    (hk : 0 < k)
    (q : InfectionRevealTraceState n)
    (hq : Lemma16TracePrefixInv v k q)
    (hbad :
      Lemma18LogicalEndBlockBad v.initialLabel E
        (InfectionRevealPrefixCheckpoint.ofTrace k q)) :
    Lemma16UrnWindowBadY rho u k R B
      (infectionRevealTraceCounts q) := by
  by_cases hreach : k ≤ q.revealed.length
  · have hlen : q.revealed.length = k := by
      have hle := hq.2
      omega
    have htake :
        q.revealed.take k = q.revealed := by
      rw [← hlen, List.take_length]
    have hbad' :
        q.revealedXIds.card <
          q.revealedYIds.card + E := by
      have hb := hbad
      simp only [InfectionRevealPrefixCheckpoint.ofTrace,
        hreach, ↓reduceIte, Lemma18LogicalEndBlockBad] at hb
      rw [htake] at hb
      rw [← hq.1] at hb
      simpa using hb
    have hxLedger :
        q.revealedXIds.card + q.current.xIds.card = B := by
      calc
        q.revealedXIds.card + q.current.xIds.card =
            q.anchor.xIds.card :=
          q.revealedX_card_add_current
        _ = v.xIds.card := by rw [hq.1]
        _ = B := hx0
    have hyLedger :
        q.revealedYIds.card + q.current.yIds.card = R := by
      calc
        q.revealedYIds.card + q.current.yIds.card =
            q.anchor.yIds.card :=
          q.revealedY_card_add_current
        _ = v.yIds.card := by rw [hq.1]
        _ = R := hy0
    have hcurrent :=
      InfectionInactiveView.xIds_card_add_yIds_card
        q.current
    have hlength := q.revealed_length_add_current
    have hanchor :
        q.anchor.ids.card = R + B := by
      calc
        q.anchor.ids.card =
            q.anchor.xIds.card + q.anchor.yIds.card := by
          rw [
            InfectionInactiveView.xIds_card_add_yIds_card]
        _ = B + R := by rw [hq.1, hx0, hy0]
        _ = R + B := by omega
    have hselected :
        q.revealedXIds.card +
            q.revealedYIds.card = k := by
      omega
    exact
      lemma18_selected_gap_bad_implies_urnWindowBadY
        rho E Gap u k R B
        q.revealedXIds.card q.revealedYIds.card
        q.current.xIds.card q.current.yIds.card
        hRB hgap hmean hselected
        hxLedger hyLedger hbad' hk
  · simp [InfectionRevealPrefixCheckpoint.ofTrace,
      hreach, Lemma18LogicalEndBlockBad] at hbad

/-- The eventual bad completed-block probability on the one-at-a-time trace
is bounded by the corresponding urn event. -/
theorem lemma18_trace_end_everHit_le_urn
    {n : ℕ} (v : InfectionInactiveView n)
    (rho E Gap u k R B : ℕ)
    (hRB : R + B = u + k + 1)
    (hgap : R + Gap ≤ B)
    (hmean : (E + rho) * (R + B) ≤ k * Gap)
    (hx0 : v.xIds.card = B)
    (hy0 : v.yIds.card = R)
    (hk : 0 < k)
    (hroom : k + 2 ≤ v.ids.card) :
    everHit
        (fun z =>
          Lemma18LogicalEndBlockBad v.initialLabel E
            (InfectionRevealPrefixCheckpoint.ofTrace k z))
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
  let Target : InfectionRevealTraceState n → Prop :=
    fun z =>
      Lemma18LogicalEndBlockBad v.initialLabel E
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
    have hurn :=
      lemma18_traceLogicalEndBad_implies_urnWindowBadY
        v rho E Gap u k R B hRB hgap hmean
        hx0 hy0 hk z hzP hz
    rw [show V z = 1 by
      exact everHit_eq_one_of_mem
        Bad urnStopped (infectionRevealTraceCounts z) hurn]
  have hinitial : P (infectionRevealTraceInitial v) := by
    exact ⟨rfl, by simp [infectionRevealTraceInitial]⟩
  have h :=
    ville_frozen_of_support_invariant
      K Target P V 1
      (by simp) (by simp)
      hcontain hclosed hsuper
      (infectionRevealTraceInitial v) hinitial
  have hcounts :
      infectionRevealTraceCounts
          (infectionRevealTraceInitial v) =
        (B, R) := by
    simp [infectionRevealTraceCounts,
      infectionRevealTraceInitial, infectionInactiveCounts,
      hx0, hy0]
  change
    everHit Target K (infectionRevealTraceInitial v) ≤
      everHit Bad urnStopped (B, R)
  unfold everHit at h ⊢
  dsimp only [V] at h
  rw [hcounts] at h
  simpa using h

/-- Logical stopped first-`k` blocks inherit the anchored trace's urn bound
through the checkpoint quotient. -/
theorem lemma18_logical_end_everHit_le_urn
    {n : ℕ} (v : InfectionInactiveView n)
    (rho E Gap u k R B : ℕ)
    (hRB : R + B = u + k + 1)
    (hgap : R + Gap ≤ B)
    (hmean : (E + rho) * (R + B) ≤ k * Gap)
    (hx0 : v.xIds.card = B)
    (hy0 : v.yIds.card = R)
    (hk : 0 < k)
    (hroom : k + 2 ≤ v.ids.card) :
    everHit
        (Lemma18LogicalEndBlockBad v.initialLabel E)
        (InfectionRevealPrefixCheckpoint.oneStep n k)
        (.live v [])
      ≤
        everHit
          (Lemma16UrnWindowBadY rho u k R B)
          urnStopped (B, R) := by
  have htrace :=
    lemma18_trace_end_everHit_le_urn
      v rho E Gap u k R B hRB hgap hmean
      hx0 hy0 hk hroom
  have hkne : k ≠ 0 := by omega
  have htransfer :
      everHit
          (fun z =>
            Lemma18LogicalEndBlockBad v.initialLabel E
              (InfectionRevealPrefixCheckpoint.ofTrace k z))
          (infectionRevealTraceFirstKStep k)
          (infectionRevealTraceInitial v) =
        everHit
          (Lemma18LogicalEndBlockBad v.initialLabel E)
          (InfectionRevealPrefixCheckpoint.oneStep n k)
          (.live v []) := by
    unfold everHit
    simpa [infectionRevealPhysicalPathInitial,
      infectionRevealTraceInitial,
      InfectionRevealPrefixCheckpoint.ofTrace, hkne] using
      iSup_hitProb_transfer
        (infectionRevealTraceFirstKStep_intertwines_checkpoint
          n k)
        (Lemma18LogicalEndBlockBad v.initialLabel E)
        (infectionRevealTraceInitial v)
  rw [← htransfer]
  exact htrace

/-- Genuine physical activation batches satisfy the strongly biased
completed-block tail on their durable first `k` identities. -/
theorem infectionRevealPhysical_lemma18_end_tail
    (n : ℕ) (h3 : 3 ≤ n)
    (qpar rho E Gap a k u nu R B : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hqa : qpar * a ≤ rho ^ 2)
    (hk : k + 1 = a)
    (huk : u + k + 1 = nu)
    (hRB : R + B = nu)
    (hquarter : 4 * a ≤ nu + 1)
    (hgap : R + Gap ≤ B)
    (hmean : (E + rho) * nu ≤ k * Gap)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk0 : 0 < k) :
    everHit
        (fun z =>
          Lemma18LogicalEndBlockBad
            s.inactive.initialLabel E
            (InfectionRevealPrefixCheckpoint.ofPhysical
              (InfectionRevealFirstKQuotient.ofPath k z)))
        (infectionRevealPhysicalFirstKStep n h3 k)
        (infectionRevealPhysicalPathInitial s)
      ≤ lemma16UrnError qpar := by
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
  have hmajor : R ≤ B := by omega
  have hmean' : (E + rho) * (R + B) ≤ k * Gap := by
    rw [hRB]
    exact hmean
  calc
    everHit
        (fun z =>
          Lemma18LogicalEndBlockBad
            s.inactive.initialLabel E
            (InfectionRevealPrefixCheckpoint.ofPhysical
              (InfectionRevealFirstKQuotient.ofPath k z)))
        (infectionRevealPhysicalFirstKStep n h3 k)
        (infectionRevealPhysicalPathInitial s)
        ≤
      everHit
        (Lemma18LogicalEndBlockBad
          s.inactive.initialLabel E)
        (InfectionRevealPrefixCheckpoint.oneStep n k)
        (.live s.inactive []) :=
      infectionRevealPhysicalFirstK_initial_everHit_le_logical
        n h3 k s hk0 hroom
          (Lemma18LogicalEndBlockBad
            s.inactive.initialLabel E)
    _ ≤
      everHit
        (Lemma16UrnWindowBadY rho u k R B)
        urnStopped (B, R) :=
      lemma18_logical_end_everHit_le_urn
        s.inactive rho E Gap u k R B hsum hgap
        hmean' hx0 hy0 hk0 hroom
    _ ≤ lemma16UrnError qpar := by
      unfold everHit
      exact
        lemma17_urn_window_tail_Y_pool
          qpar rho a k u nu R B
          hqa hk huk hRB hquarter hk0

/-- Removing a possible one-identity physical overshoot costs one unit from
the required positive block gap. -/
theorem lemma18_word_gap_bad_drop_one
    {n : ℕ} (label : Fin n → InfectionLabel)
    (E k : ℕ) (word : List (Fin n))
    (hnodup : word.Nodup)
    (hlen : word.length ≤ k + 1)
    (hklen : k < word.length)
    (hbad :
      infectionRevealWordXCount label word <
        infectionRevealWordYCount label word + E) :
    infectionRevealWordXCount label (word.take k) <
      infectionRevealWordYCount label (word.take k) +
        (E + 1) := by
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
    infectionRevealWordXCount label pref <
      infectionRevealWordYCount label pref + (E + 1)
  omega

/-- A reached physical block failure is visible on the durable first-`k`
checkpoint after reserving one unit for overshoot. -/
theorem lemma18EndBlockBad_implies_logical
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (k A G E : ℕ)
    (hanchorActive : s.coarse.1.active + k = A)
    (q : Lemma17CountedPathState n)
    (hinv : Lemma17CountedPathInv s k A G q)
    (hreached :
      A ≤ q.counted.path.current.coarse.1.active)
    (hbad : Lemma18EndBlockBad E q) :
    Lemma18LogicalEndBlockBad
      s.inactive.initialLabel (E + 1)
      (InfectionRevealPrefixCheckpoint.ofPhysical
        (InfectionRevealFirstKQuotient.ofPath
          k q.counted.path)) := by
  have hanchor : q.counted.path.anchor = s := hinv.1.1
  have hphysicalLedger := q.counted.path.hactiveLedger
  have hkreached :
      k ≤ q.counted.path.revealed.length := by
    rw [hanchor] at hphysicalLedger
    omega
  have hbadWord :
      infectionRevealWordXCount
            s.inactive.initialLabel
            q.counted.path.revealed <
        infectionRevealWordYCount
              s.inactive.initialLabel
              q.counted.path.revealed +
            E := by
    unfold Lemma18EndBlockBad at hbad
    rw [hanchor] at hbad
    exact hbad
  simp only [InfectionRevealFirstKQuotient.ofPath,
    hkreached, if_pos,
    InfectionRevealPrefixCheckpoint.ofPhysical,
    InfectionRevealPrefixCheckpoint.word,
    Lemma18LogicalEndBlockBad]
  by_cases hlen :
      q.counted.path.revealed.length ≤ k
  · have heq :
        q.counted.path.revealed.length = k := by
      omega
    rw [← heq, List.take_length]
    omega
  · have hklen :
        k < q.counted.path.revealed.length := by
      omega
    exact
      lemma18_word_gap_bad_drop_one
        s.inactive.initialLabel E k
        q.counted.path.revealed
        q.counted.path.hnodup hinv.1.2 hklen hbadWord

/-- The strong completed-block urn tail transfers to the joint counted
physical path.  The block condition is required only after the activation
target has been reached; unreached mass belongs to the separate clock term. -/
theorem lemma18CountedPath_end_tail
    (n : ℕ) (h3 : 3 ≤ n)
    (qpar rho E Gap a k u nu R B A G T : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + k = A)
    (hqa : qpar * a ≤ rho ^ 2)
    (hk : k + 1 = a)
    (huk : u + k + 1 = nu)
    (hRB : R + B = nu)
    (hquarter : 4 * a ≤ nu + 1)
    (hgap : R + Gap ≤ B)
    (hmean : ((E + 1) + rho) * nu ≤ k * Gap)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk0 : 0 < k) :
    terminalFailureMass
        (iter (lemma17CountedPathStep n h3 k A G) T
          (lemma17CountedPathInitial s))
        (fun z =>
          A ≤ z.counted.path.current.coarse.1.active →
            ¬ Lemma18EndBlockBad E z)
      ≤ lemma16UrnError qpar := by
  let K := lemma17CountedPathStep n h3 k A G
  let q₀ := lemma17CountedPathInitial s
  let μ := iter K T q₀
  let Reached : Lemma17CountedPathState n → Prop :=
    fun z => A ≤ z.counted.path.current.coarse.1.active
  let EndBad : Lemma17CountedPathState n → Prop :=
    fun z => Reached z ∧ Lemma18EndBlockBad E z
  let PathBad : InfectionRevealPhysicalPathState n → Prop :=
    fun z =>
      Lemma18LogicalEndBlockBad
        s.inactive.initialLabel (E + 1)
        (InfectionRevealPrefixCheckpoint.ofPhysical
          (InfectionRevealFirstKQuotient.ofPath k z))
  let P : Lemma17CountedPathState n → Prop :=
    Lemma17CountedPathInv s k A G
  have hclosed :
      ∀ x, P x → ∀ y, K x y ≠ 0 → P y := by
    intro x hx y hy
    exact
      lemma17CountedPathStep_inv_closed
        n h3 k A G s hanchorActive x y hx hy
  have hcontain :
      ∀ z, P z → EndBad z →
        PathBad (lemma17CountedPathToPath z) := by
    intro z hz hbad
    exact
      lemma18EndBlockBad_implies_logical
        s k A G E hanchorActive z hz hbad.1 hbad.2
  have hinitial : P q₀ :=
    lemma17CountedPathInitial_inv s k A G
  have hterminal :
      terminalFailureMass μ (fun z => ¬ EndBad z) ≤
        hitProb EndBad K T q₀ :=
    terminalEventMass_iter_le_hitProb
      EndBad K T q₀
  have hmono :
      hitProb EndBad K T q₀ ≤
        hitProb
          (fun z =>
            PathBad (lemma17CountedPathToPath z))
          K T q₀ :=
    hitProb_mono_target_of_support_invariant
      K EndBad
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
      infectionRevealPhysical_lemma18_end_tail
        n h3 qpar rho (E + 1) Gap
        a k u nu R B s
        hqa hk huk hRB hquarter hgap
        hmean hx0 hy0 hk0
  calc
    terminalFailureMass
          (iter (lemma17CountedPathStep n h3 k A G) T
            (lemma17CountedPathInitial s))
          (fun z =>
            A ≤ z.counted.path.current.coarse.1.active →
              ¬ Lemma18EndBlockBad E z) =
        terminalFailureMass μ (fun z => ¬ EndBad z) := by
          congr 1
          funext z
          simp [EndBad, Reached]
    _ ≤ hitProb EndBad K T q₀ := hterminal
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

/-- Paper constants for the decisive block.  The overshoot reserve is
absorbed by the subtraction-free witness `rho + 1 = 12D`, so the exact mean
budget remains `48D + 12D = 60D`. -/
theorem lemma18CountedPath_paper_end_tail
    (n : ℕ) (h3 : 3 ≤ n)
    (qpar rho D d k u nu R B A T : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + k = A)
    (hrho : rho + 1 = 12 * D)
    (hqa : qpar * (k + 1) ≤ rho ^ 2)
    (huk : u + k + 1 = nu)
    (hRB : R + B = nu)
    (hquarter : 4 * (k + 1) ≤ nu + 1)
    (hpoolScale : nu ≤ k * d)
    (hgap : R + 60 * d * D ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk0 : 0 < k) :
    terminalFailureMass
        (iter
          (lemma17CountedPathStep n h3 k A (30 * D)) T
          (lemma17CountedPathInitial s))
        (fun z =>
          A ≤ z.counted.path.current.coarse.1.active →
            ¬ Lemma18EndBlockBad (48 * D) z)
      ≤ lemma16UrnError qpar := by
  have hcoeff :
      (48 * D + 1) + rho = 60 * D := by
    omega
  have hmean :
      (((48 * D) + 1) + rho) * nu ≤
        k * (60 * d * D) := by
    rw [hcoeff]
    calc
      60 * D * nu ≤ 60 * D * (k * d) :=
        Nat.mul_le_mul_left (60 * D) hpoolScale
      _ = k * (60 * d * D) := by ring
  exact
    lemma18CountedPath_end_tail
      n h3 qpar rho (48 * D) (60 * d * D)
      (k + 1) k u nu R B A (30 * D) T s
      hanchorActive hqa rfl huk hRB hquarter hgap
      hmean hx0 hy0 hk0

end

end Tri

#print axioms Tri.lemma18_selected_gap_bad_implies_urnWindowBadY
#print axioms Tri.lemma18_traceLogicalEndBad_implies_urnWindowBadY
#print axioms Tri.lemma18_trace_end_everHit_le_urn
#print axioms Tri.lemma18_logical_end_everHit_le_urn
#print axioms Tri.infectionRevealPhysical_lemma18_end_tail
#print axioms Tri.lemma18_word_gap_bad_drop_one
#print axioms Tri.lemma18EndBlockBad_implies_logical
#print axioms Tri.lemma18CountedPath_end_tail
#print axioms Tri.lemma18CountedPath_paper_end_tail
