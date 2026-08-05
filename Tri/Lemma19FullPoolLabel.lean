/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma19UrnLabel
import Tri.Lemma17LabelTail

/-!
# Full-pool label tails on reveal traces and physical paths

The last two possible prefix lengths cannot have positive adverse excess when
the initial inactive population has an `X` majority.  Consequently the
existing physical first-`k` time change can stop with exactly two identities
left, while the fixed-time urn union controls the whole pool.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- A bad current trace prefix is exactly a selected-label excess in the
remaining-count urn. -/
theorem lemma19_traceCurrentBad_implies_urnSelectedYExcessBad
    {n : ℕ} (v : InfectionInactiveView n)
    (D k B R : ℕ)
    (hx0 : v.xIds.card = B)
    (hy0 : v.yIds.card = R)
    (z : InfectionRevealTraceState n)
    (hz : Lemma16TracePrefixInv v k z)
    (hbad : Lemma17TraceCurrentLabelBad D z) :
    UrnSelectedYExcessBad D B R
      (infectionRevealTraceCounts z) := by
  have hxLedger :
      z.revealedXIds.card +
          z.current.xIds.card = B := by
    calc
      z.revealedXIds.card +
            z.current.xIds.card =
          z.anchor.xIds.card :=
        z.revealedX_card_add_current
      _ = v.xIds.card := by rw [hz.1]
      _ = B := hx0
  have hyLedger :
      z.revealedYIds.card +
          z.current.yIds.card = R := by
    calc
      z.revealedYIds.card +
            z.current.yIds.card =
          z.anchor.yIds.card :=
        z.revealedY_card_add_current
      _ = v.yIds.card := by rw [hz.1]
      _ = R := hy0
  refine
    ⟨z.revealedXIds.card,
      z.revealedYIds.card, ?_, ?_, ?_⟩
  · simpa [infectionRevealTraceCounts,
      infectionInactiveCounts] using hxLedger
  · simpa [infectionRevealTraceCounts,
      infectionInactiveCounts] using hyLedger
  · simpa [Lemma17TraceCurrentLabelBad] using hbad

/-- Current-prefix failure on a stopped reveal trace is dominated by the
full-pool selected-excess urn event. -/
theorem lemma19_trace_current_prefix_everHit_le_urn
    {n : ℕ} (v : InfectionInactiveView n)
    (D k B R : ℕ)
    (hx0 : v.xIds.card = B)
    (hy0 : v.yIds.card = R)
    (hroom : k + 2 ≤ v.ids.card) :
    everHit
        (Lemma17TraceCurrentLabelBad D)
        (infectionRevealTraceFirstKStep k)
        (infectionRevealTraceInitial v)
      ≤
    everHit
        (UrnSelectedYExcessBad D B R)
        urnStopped (B, R) := by
  let Bad := UrnSelectedYExcessBad D B R
  let K := @infectionRevealTraceFirstKStep n k
  let P := Lemma16TracePrefixInv v k
  let V : InfectionRevealTraceState n → ℝ≥0∞ :=
    fun z =>
      everHit Bad urnStopped
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
      ∀ z, P z → Lemma17TraceCurrentLabelBad D z →
        (1 : ℝ≥0∞) ≤ V z := by
    intro z hzP hz
    have hurn :=
      lemma19_traceCurrentBad_implies_urnSelectedYExcessBad
        v D k B R hx0 hy0 z hzP hz
    rw [show V z = 1 by
      exact everHit_eq_one_of_mem
        Bad urnStopped
        (infectionRevealTraceCounts z) hurn]
  have hinitial :
      P (infectionRevealTraceInitial v) :=
    ⟨rfl, by simp [infectionRevealTraceInitial]⟩
  have h :=
    ville_frozen_of_support_invariant
      K (Lemma17TraceCurrentLabelBad D)
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

/-- The logical historical-prefix event inherits the full-pool urn tail. -/
theorem lemma19_logical_max_prefix_everHit_le_urn
    {n : ℕ} (v : InfectionInactiveView n)
    (D k B R : ℕ)
    (hx0 : v.xIds.card = B)
    (hy0 : v.yIds.card = R)
    (hk : 0 < k)
    (hroom : k + 2 ≤ v.ids.card) :
    everHit
        (Lemma17LogicalMaxLabelBad
          v.initialLabel D)
        (InfectionRevealPrefixCheckpoint.oneStep n k)
        (.live v [])
      ≤
    everHit
        (UrnSelectedYExcessBad D B R)
        urnStopped (B, R) := by
  let K := @infectionRevealTraceFirstKStep n k
  let P := Lemma16TracePrefixInv v k
  let QuotientBad : InfectionRevealTraceState n → Prop :=
    fun z =>
      Lemma17LogicalMaxLabelBad
        v.initialLabel D
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
          (Lemma17TraceMaxLabelBad D) K
          (infectionRevealTraceInitial v) := by
    apply
      everHit_mono_target_of_support_invariant
        K QuotientBad
        (Lemma17TraceMaxLabelBad D) P
        hclosed
    · intro z hzP hz
      exact
        lemma17_logicalMaxBad_implies_traceMaxBad
          v D k z hzP hz
    · exact
        ⟨rfl, by
          simp [infectionRevealTraceInitial]⟩
  have hmaxCurrent :
      everHit
          (Lemma17TraceMaxLabelBad D) K
          (infectionRevealTraceInitial v) ≤
        everHit
          (Lemma17TraceCurrentLabelBad D) K
          (infectionRevealTraceInitial v) := by
    apply lemma17_trace_max_everHit_le_current
    simp [Lemma17TraceMaxLabelBad,
      lemma17WordPrefixBad,
      infectionRevealTraceInitial,
      infectionRevealWordXCount,
      infectionRevealWordYCount]
  have hcurrent :=
    lemma19_trace_current_prefix_everHit_le_urn
      v D k B R hx0 hy0 hroom
  have hkne : k ≠ 0 := by omega
  have htransfer :
      everHit QuotientBad K
          (infectionRevealTraceInitial v) =
        everHit
          (Lemma17LogicalMaxLabelBad
            v.initialLabel D)
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
          v.initialLabel D)
        (infectionRevealTraceInitial v)
  rw [← htransfer]
  exact hmono.trans (hmaxCurrent.trans hcurrent)

/-- Physical activation batches satisfy the full-pool maximal label tail.
The requested prefix stops with two identities left; the urn bound itself
runs through its one-ball floor. -/
theorem infectionRevealPhysical_lemma19_full_prefix_tail
    (n : ℕ) (h3 : 3 ≤ n)
    (L : ℝ) (D k B R : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hD : 0 < D)
    (hk : 0 < k)
    (hpool : k + 2 = B + R)
    (hmajor : R ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hscale :
      L * ((B + R : ℕ) : ℝ) ≤
        ((D : ℝ) / 2) ^ 2) :
    everHit
        (fun z =>
          Lemma17LogicalMaxLabelBad
            s.inactive.initialLabel D
            (InfectionRevealPrefixCheckpoint.ofPhysical
              (InfectionRevealFirstKQuotient.ofPath k z)))
        (infectionRevealPhysicalFirstKStep n h3 k)
        (infectionRevealPhysicalPathInitial s)
      ≤
    (k + 2 : ℝ≥0∞) *
      (2 * ENNReal.ofReal (Real.exp (-L))) := by
  have hidscard :
      s.inactive.ids.card = B + R := by
    calc
      s.inactive.ids.card =
          s.inactive.xIds.card +
            s.inactive.yIds.card := by
        rw [
          InfectionInactiveView.xIds_card_add_yIds_card]
      _ = B + R := by omega
  have hroom : k + 2 ≤ s.inactive.ids.card := by
    omega
  calc
    everHit
        (fun z =>
          Lemma17LogicalMaxLabelBad
            s.inactive.initialLabel D
            (InfectionRevealPrefixCheckpoint.ofPhysical
              (InfectionRevealFirstKQuotient.ofPath k z)))
        (infectionRevealPhysicalFirstKStep n h3 k)
        (infectionRevealPhysicalPathInitial s)
        ≤
      everHit
        (Lemma17LogicalMaxLabelBad
          s.inactive.initialLabel D)
        (InfectionRevealPrefixCheckpoint.oneStep n k)
        (.live s.inactive []) :=
      infectionRevealPhysicalFirstK_initial_everHit_le_logical
        n h3 k s hk hroom
          (Lemma17LogicalMaxLabelBad
            s.inactive.initialLabel D)
    _ ≤
      everHit
        (UrnSelectedYExcessBad D B R)
        urnStopped (B, R) :=
      lemma19_logical_max_prefix_everHit_le_urn
        s.inactive D k B R hx0 hy0 hk hroom
    _ ≤
      (k + 2 : ℝ≥0∞) *
        (2 * ENNReal.ofReal (Real.exp (-L))) := by
      convert
        urnSelectedYExcess_everHit
          L D (k + 1) B R
          hD hmajor (by omega) hscale using 1 <;>
        push_cast <;> ring

end

end Tri

#print axioms Tri.lemma19_traceCurrentBad_implies_urnSelectedYExcessBad
#print axioms Tri.lemma19_trace_current_prefix_everHit_le_urn
#print axioms Tri.lemma19_logical_max_prefix_everHit_le_urn
#print axioms Tri.infectionRevealPhysical_lemma19_full_prefix_tail
