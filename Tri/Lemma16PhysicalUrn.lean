/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionRevealPhysicalHitting
import Tri.InfectionRevealTrace
import Tri.Lemma16Label
import Tri.Lemma16Urn

/-!
# Physical activation prefixes and the Lemma 16 urn event

This file connects the genuine zero/one/two-activation physical clock to the
negative-tilt urn tail.  The adverse immutable label `Y` is the second
coordinate of `infectionInactiveCounts`.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Number of distinct identities in a word carrying immutable label `X`. -/
def infectionRevealWordXCount
    {n : ℕ} (label : Fin n → InfectionLabel)
    (word : List (Fin n)) : ℕ :=
  (word.toFinset.filter fun i => label i = .X).card

/-- Number of distinct identities in a word carrying immutable label `Y`. -/
def infectionRevealWordYCount
    {n : ℕ} (label : Fin n → InfectionLabel)
    (word : List (Fin n)) : ℕ :=
  (word.toFinset.filter fun i => label i = .Y).card

/-- A completed logical prefix has adverse `Y` excess greater than `rho`. -/
def Lemma16LogicalPrefixBad
    {n : ℕ} (label : Fin n → InfectionLabel)
    (rho : ℕ) :
    InfectionRevealPrefixCheckpoint n → Prop
  | .live _ _ => False
  | .done word =>
      infectionRevealWordXCount label word + rho <
        infectionRevealWordYCount label word

noncomputable instance
    {n : ℕ} (label : Fin n → InfectionLabel) (rho : ℕ) :
    DecidablePred (Lemma16LogicalPrefixBad label rho) :=
  Classical.decPred _

/-- A bad selected-label prefix forces the negative-tilt urn event at the
corresponding remaining counts. -/
theorem lemma16_selected_bad_implies_urnWindowBadY
    (rho u k R B xSel ySel xRem yRem : ℕ)
    (hRB : R + B = u + k + 1)
    (hmajor : R ≤ B)
    (hselected : xSel + ySel = k)
    (hx : xSel + xRem = B)
    (hy : ySel + yRem = R)
    (hbad : xSel + rho < ySel)
    (hk : 0 < k) :
    Lemma16UrnWindowBadY rho u k R B (xRem, yRem) := by
  have hnu : 0 < R + B := by omega
  have hdev :=
    lemma16_newLabelBad_implies_centeredRed
      R B (R + B) k xSel ySel rho
      hnu rfl hmajor hselected hbad
  have hrem : xRem + yRem = u + 1 := by omega
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
    exact_mod_cast (show xRem + yRem ≤ R + B by omega)
  let num : ℝ :=
    (ySel : ℝ) -
      (k : ℝ) * ((R : ℝ) / ((R : ℝ) + (B : ℝ)))
  have hnum :
      (rho : ℝ) / 2 ≤ num := by
    simpa only [Nat.cast_add] using hdev.le
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
    field_simp [ne_of_gt hremPosR, ne_of_gt hnuPosR]
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
        (div_le_div_iff_of_pos_right hnuPosR).2 hnum
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
      nlinarith [hnuPosR]
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

@[simp] theorem infectionRevealWordXCount_revealed
    {n : ℕ} (q : InfectionRevealTraceState n) :
    infectionRevealWordXCount q.anchor.initialLabel q.revealed =
      q.revealedXIds.card :=
  rfl

@[simp] theorem infectionRevealWordYCount_revealed
    {n : ℕ} (q : InfectionRevealTraceState n) :
    infectionRevealWordYCount q.anchor.initialLabel q.revealed =
      q.revealedYIds.card :=
  rfl

/-- Reachable trace states retain their chosen anchor and never overshoot the
one-at-a-time prefix length. -/
def Lemma16TracePrefixInv
    {n : ℕ} (v : InfectionInactiveView n) (k : ℕ)
    (q : InfectionRevealTraceState n) : Prop :=
  q.anchor = v ∧ q.revealed.length ≤ k

/-- The stopped one-at-a-time trace preserves its anchor/length invariant on
support. -/
theorem infectionRevealTraceFirstKStep_prefixInv_closed
    {n : ℕ} (v : InfectionInactiveView n) (k : ℕ)
    (q z : InfectionRevealTraceState n)
    (hq : Lemma16TracePrefixInv v k q)
    (hz : infectionRevealTraceFirstKStep k q z ≠ 0) :
    Lemma16TracePrefixInv v k z := by
  by_cases hreach : InfectionRevealTraceReached k q
  · have hzq : z = q := by
      unfold infectionRevealTraceFirstKStep at hz
      rw [freeze_of_mem q hreach] at hz
      by_contra hne
      simp [PMF.pure_apply, hne] at hz
    simpa [hzq] using hq
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
      refine ⟨hq.1, ?_⟩
      simp only [InfectionRevealTraceState.afterOne,
        List.length_append, List.length_cons, List.length_nil]
      have hlt : q.revealed.length < k := by
        simpa [InfectionRevealTraceReached] using hreach
      omega
    · rw [dif_neg hcard] at hz
      have hzq : z = q := by
        by_contra hne
        simp [PMF.pure_apply, hne] at hz
      simpa [hzq] using hq

/-- The eventual urn hitting probability, pulled back to an anchored reveal
trace, is superharmonic until the first `k` reveals. -/
theorem expect_infectionRevealTraceFirstKStep_urnEverHit_le
    {n : ℕ} (v : InfectionInactiveView n) (k : ℕ)
    (hroom : k + 2 ≤ v.ids.card)
    (Bad : ℕ × ℕ → Prop) [DecidablePred Bad]
    (q : InfectionRevealTraceState n)
    (hq : Lemma16TracePrefixInv v k q) :
    expect
        (infectionRevealTraceFirstKStep k q)
        (fun z =>
          everHit Bad urnStopped
            (infectionRevealTraceCounts z))
      ≤
        everHit Bad urnStopped
          (infectionRevealTraceCounts q) := by
  by_cases hreach : InfectionRevealTraceReached k q
  · unfold infectionRevealTraceFirstKStep
    rw [freeze_of_mem q hreach, expect_pure]
  · have hlt : q.revealed.length < k := by
      simpa [InfectionRevealTraceReached] using hreach
    have hledger := q.revealed_length_add_current
    have hanchor : q.anchor.ids.card = v.ids.card := by
      rw [hq.1]
    have hcurrent : 2 < q.current.ids.card := by
      omega
    have hcountTotal :
        (infectionRevealTraceCounts q).1 +
            (infectionRevealTraceCounts q).2 =
          q.current.ids.card := by
      exact
        InfectionInactiveView.xIds_card_add_yIds_card
          q.current
    have hnotStopped :
        ¬ (infectionRevealTraceCounts q).1 +
            (infectionRevealTraceCounts q).2 ≤ 1 := by
      omega
    have hstep :
        infectionRevealTraceFirstKStep k q =
          infectionRevealTraceStep q := by
      unfold infectionRevealTraceFirstKStep
      rw [freeze_of_not_mem q hreach]
    have hurn :
        urnStopped (infectionRevealTraceCounts q) =
          urnChain (infectionRevealTraceCounts q) := by
      unfold urnStopped
      rw [freeze_of_not_mem
        (infectionRevealTraceCounts q) hnotStopped]
    rw [hstep]
    calc
      expect
          (infectionRevealTraceStep q)
          (fun z =>
            everHit Bad urnStopped
              (infectionRevealTraceCounts z)) =
        expect
          ((infectionRevealTraceStep q).map
            infectionRevealTraceCounts)
          (everHit Bad urnStopped) := by
            rw [expect_map]
      _ =
        expect
          (urnChain (infectionRevealTraceCounts q))
          (everHit Bad urnStopped) := by
            rw [
              infectionRevealTraceStep_intertwines_urnChain n q]
      _ =
        expect
          (urnStopped (infectionRevealTraceCounts q))
          (everHit Bad urnStopped) := by
            rw [hurn]
      _ ≤
        everHit Bad urnStopped
          (infectionRevealTraceCounts q) :=
        expect_everHit_le Bad urnStopped
          (infectionRevealTraceCounts q)

/-- On a valid stopped trace, a bad logical completed prefix is contained in
the negative-tilt urn event on the remaining `(X,Y)` counts. -/
theorem lemma16_traceLogicalBad_implies_urnWindowBadY
    {n : ℕ} (v : InfectionInactiveView n)
    (rho u k R B : ℕ)
    (hRB : R + B = u + k + 1)
    (hmajor : R ≤ B)
    (hx0 : v.xIds.card = B)
    (hy0 : v.yIds.card = R)
    (hk : 0 < k)
    (q : InfectionRevealTraceState n)
    (hq : Lemma16TracePrefixInv v k q)
    (hbad :
      Lemma16LogicalPrefixBad v.initialLabel rho
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
        q.revealedXIds.card + rho <
          q.revealedYIds.card := by
      have hb := hbad
      simp only [InfectionRevealPrefixCheckpoint.ofTrace,
        hreach, ↓reduceIte, Lemma16LogicalPrefixBad] at hb
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
      lemma16_selected_bad_implies_urnWindowBadY
        rho u k R B
        q.revealedXIds.card q.revealedYIds.card
        q.current.xIds.card q.current.yIds.card
        hRB hmajor hselected hxLedger hyLedger hbad' hk
  · simp [InfectionRevealPrefixCheckpoint.ofTrace,
      hreach, Lemma16LogicalPrefixBad] at hbad

/-- Eventual bad-prefix probability on the anchored one-at-a-time trace is
bounded by the corresponding maximal urn event. -/
theorem lemma16_trace_prefix_everHit_le_urn
    {n : ℕ} (v : InfectionInactiveView n)
    (rho u k R B : ℕ)
    (hRB : R + B = u + k + 1)
    (hmajor : R ≤ B)
    (hx0 : v.xIds.card = B)
    (hy0 : v.yIds.card = R)
    (hk : 0 < k)
    (hroom : k + 2 ≤ v.ids.card) :
    everHit
        (fun z =>
          Lemma16LogicalPrefixBad v.initialLabel rho
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
      Lemma16LogicalPrefixBad v.initialLabel rho
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
      lemma16_traceLogicalBad_implies_urnWindowBadY
        v rho u k R B hRB hmajor hx0 hy0 hk z
        hzP hz
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

/-- Logical stopped one-at-a-time prefixes inherit the anchored trace's urn
bound exactly through the checkpoint quotient. -/
theorem lemma16_logical_prefix_everHit_le_urn
    {n : ℕ} (v : InfectionInactiveView n)
    (rho u k R B : ℕ)
    (hRB : R + B = u + k + 1)
    (hmajor : R ≤ B)
    (hx0 : v.xIds.card = B)
    (hy0 : v.yIds.card = R)
    (hk : 0 < k)
    (hroom : k + 2 ≤ v.ids.card) :
    everHit
        (Lemma16LogicalPrefixBad v.initialLabel rho)
        (InfectionRevealPrefixCheckpoint.oneStep n k)
        (.live v [])
      ≤
        everHit
          (Lemma16UrnWindowBadY rho u k R B)
          urnStopped (B, R) := by
  have htrace :=
    lemma16_trace_prefix_everHit_le_urn
      v rho u k R B hRB hmajor hx0 hy0 hk hroom
  have hkne : k ≠ 0 := by omega
  have htransfer :
      everHit
          (fun z =>
            Lemma16LogicalPrefixBad v.initialLabel rho
              (InfectionRevealPrefixCheckpoint.ofTrace k z))
          (infectionRevealTraceFirstKStep k)
          (infectionRevealTraceInitial v) =
        everHit
          (Lemma16LogicalPrefixBad v.initialLabel rho)
          (InfectionRevealPrefixCheckpoint.oneStep n k)
          (.live v []) := by
    unfold everHit
    simpa [infectionRevealPhysicalPathInitial,
      infectionRevealTraceInitial,
      InfectionRevealPrefixCheckpoint.ofTrace, hkne] using
      iSup_hitProb_transfer
        (infectionRevealTraceFirstKStep_intertwines_checkpoint
          n k)
        (Lemma16LogicalPrefixBad v.initialLabel rho)
        (infectionRevealTraceInitial v)
  rw [← htransfer]
  exact htrace

/-- Genuine physical activation batches satisfy the Lemma 16 immutable-label
prefix tail. -/
theorem infectionRevealPhysical_lemma16_prefix_tail
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
          Lemma16LogicalPrefixBad
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
          Lemma16LogicalPrefixBad
            s.inactive.initialLabel rho
            (InfectionRevealPrefixCheckpoint.ofPhysical
              (InfectionRevealFirstKQuotient.ofPath k z)))
        (infectionRevealPhysicalFirstKStep n h3 k)
        (infectionRevealPhysicalPathInitial s)
        ≤
      everHit
        (Lemma16LogicalPrefixBad
          s.inactive.initialLabel rho)
        (InfectionRevealPrefixCheckpoint.oneStep n k)
        (.live s.inactive []) :=
      infectionRevealPhysicalFirstK_initial_everHit_le_logical
        n h3 k s hk0 hroom
          (Lemma16LogicalPrefixBad
            s.inactive.initialLabel rho)
    _ ≤
      everHit
        (Lemma16UrnWindowBadY rho u k R B)
        urnStopped (B, R) :=
      lemma16_logical_prefix_everHit_le_urn
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

#print axioms Tri.lemma16_selected_bad_implies_urnWindowBadY
#print axioms Tri.infectionRevealWordXCount_revealed
#print axioms Tri.infectionRevealWordYCount_revealed
#print axioms Tri.infectionRevealTraceFirstKStep_prefixInv_closed
#print axioms Tri.expect_infectionRevealTraceFirstKStep_urnEverHit_le
#print axioms Tri.lemma16_traceLogicalBad_implies_urnWindowBadY
#print axioms Tri.lemma16_trace_prefix_everHit_le_urn
#print axioms Tri.lemma16_logical_prefix_everHit_le_urn
#print axioms Tri.infectionRevealPhysical_lemma16_prefix_tail
