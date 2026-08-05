/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionRevealPhysicalUpdate
import Tri.Emulation

/-!
# The identity-refined physical infection step

Positive activation witnesses update the remaining inactive view by exact
one- or two-identity erasure. Active-only events retain that view. The
resulting total kernel projects exactly to the original coarse infection
kernel.
-/

namespace Tri

/-- Apply a positive event that leaves all inactive counts unchanged. -/
noncomputable def infectionRevealPhysicalPreserve
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (e : InfectionEvent)
    (he : InfectionEvent.weight s.coarse.1 e ≠ 0)
    (hix : (InfectionEvent.next s.coarse.1 e).ix =
      s.coarse.1.ix)
    (hiy : (InfectionEvent.next s.coarse.1 e).iy =
      s.coarse.1.iy) :
    InfectionRevealPhysicalState n where
  coarse := InfectionEvent.nextState s.coarse e
  inactive := s.inactive
  hinactiveCard := by
    unfold InfectionEvent.nextState
    rw [dif_neg he]
    rw [s.hinactiveCard]
    simp only [InfectionCfg.inactive]
    rw [hix, hiy]
  hinactiveX := by
    unfold InfectionEvent.nextState
    rw [dif_neg he]
    simpa only [hix] using s.hinactiveX
  hinactiveY := by
    unfold InfectionEvent.nextState
    rw [dif_neg he]
    simpa only [hiy] using s.hinactiveY

/-- Apply a positive one-`X` activation witness. -/
noncomputable def infectionRevealPhysicalActivateOneX
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (i : InfectionInactiveXId s)
    (he : InfectionEvent.weight s.coarse.1 .activateOneX ≠ 0) :
    InfectionRevealPhysicalState n where
  coarse := InfectionEvent.nextState s.coarse .activateOneX
  inactive := s.inactive.erase (infectionInactiveXToId i)
  hinactiveCard := by
    have herase :=
      s.inactive.erase_card_add_one (infectionInactiveXToId i)
    have hixpos : 0 < s.coarse.1.ix := by
      have : 0 < s.inactive.xIds.card :=
        Finset.card_pos.mpr ⟨i.1, i.2⟩
      rw [s.hinactiveX] at this
      exact this
    unfold InfectionEvent.nextState
    rw [dif_neg he]
    simp only [InfectionEvent.next, InfectionCfg.inactive]
    have hcard := s.hinactiveCard
    simp only [InfectionCfg.inactive] at hcard
    omega
  hinactiveX := by
    have hiX :
        (infectionInactiveXToId i).1 ∈ s.inactive.xIds :=
      i.2
    rw [InfectionInactiveView.erase_xIds,
      Finset.card_erase_of_mem hiX]
    unfold InfectionEvent.nextState
    rw [dif_neg he]
    simp only [InfectionEvent.next]
    rw [← s.hinactiveX]
  hinactiveY := by
    have hnot :
        (infectionInactiveXToId i).1 ∉ s.inactive.yIds := by
      intro hiY
      have hy := (Finset.mem_filter.mp hiY).2
      have hx := infectionInactiveXToId_label i
      rw [hx] at hy
      contradiction
    rw [InfectionInactiveView.erase_yIds,
      Finset.erase_eq_of_notMem hnot]
    unfold InfectionEvent.nextState
    rw [dif_neg he]
    simpa only [InfectionEvent.next] using s.hinactiveY

/-- Apply a positive one-`Y` activation witness. -/
noncomputable def infectionRevealPhysicalActivateOneY
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (i : InfectionInactiveYId s)
    (he : InfectionEvent.weight s.coarse.1 .activateOneY ≠ 0) :
    InfectionRevealPhysicalState n where
  coarse := InfectionEvent.nextState s.coarse .activateOneY
  inactive := s.inactive.erase (infectionInactiveYToId i)
  hinactiveCard := by
    have herase :=
      s.inactive.erase_card_add_one (infectionInactiveYToId i)
    have hiypos : 0 < s.coarse.1.iy := by
      have : 0 < s.inactive.yIds.card :=
        Finset.card_pos.mpr ⟨i.1, i.2⟩
      rw [s.hinactiveY] at this
      exact this
    unfold InfectionEvent.nextState
    rw [dif_neg he]
    simp only [InfectionEvent.next, InfectionCfg.inactive]
    have hcard := s.hinactiveCard
    simp only [InfectionCfg.inactive] at hcard
    omega
  hinactiveX := by
    have hnot :
        (infectionInactiveYToId i).1 ∉ s.inactive.xIds := by
      intro hiX
      have hx := (Finset.mem_filter.mp hiX).2
      have hy := infectionInactiveYToId_label i
      rw [hy] at hx
      contradiction
    rw [InfectionInactiveView.erase_xIds,
      Finset.erase_eq_of_notMem hnot]
    unfold InfectionEvent.nextState
    rw [dif_neg he]
    simpa only [InfectionEvent.next] using s.hinactiveX
  hinactiveY := by
    have hiY :
        (infectionInactiveYToId i).1 ∈ s.inactive.yIds :=
      i.2
    rw [InfectionInactiveView.erase_yIds,
      Finset.card_erase_of_mem hiY]
    unfold InfectionEvent.nextState
    rw [dif_neg he]
    simp only [InfectionEvent.next]
    rw [← s.hinactiveY]

/-- Apply a positive ordered `XX` activation witness. -/
noncomputable def infectionRevealPhysicalActivateTwoXX
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (p : InfectionInactiveXX s)
    (he : InfectionEvent.weight s.coarse.1 .activateTwoXX ≠ 0) :
    InfectionRevealPhysicalState n := by
  let op := infectionInactiveXXToOrdered p
  have hchoose : Nat.choose s.coarse.1.ix 2 ≠ 0 :=
    (Nat.mul_ne_zero_iff.mp (by
      simpa only [InfectionEvent.weight] using he)).2
  have hix2 : 2 ≤ s.coarse.1.ix :=
    Nat.choose_ne_zero_iff.mp hchoose
  have hx :
      s.inactive.xIds.card =
        (s.coarse.1.ix - 2) + 2 := by
    rw [s.hinactiveX]
    omega
  have hfirst :
      s.inactive.initialLabel op.1.1.1 = .X := by
    exact infectionInactiveXToId_label p.1.1
  have hsecond :
      s.inactive.initialLabel op.1.2.1 = .X := by
    exact infectionInactiveXToId_label p.1.2
  have hcounts :=
    infectionRevealEraseTwo_counts_XX
      s.inactive op hfirst hsecond hx s.hinactiveY
  exact
    { coarse :=
        InfectionEvent.nextState s.coarse .activateTwoXX
      inactive := infectionRevealEraseTwo s.inactive op
      hinactiveCard := by
        have herase :=
          infectionRevealEraseTwo_card_add_two s.inactive op
        have hcard := s.hinactiveCard
        simp only [InfectionCfg.inactive] at hcard
        unfold InfectionEvent.nextState
        rw [dif_neg he]
        simp only [InfectionEvent.next, InfectionCfg.inactive]
        omega
      hinactiveX := by
        unfold InfectionEvent.nextState
        rw [dif_neg he]
        simpa only [InfectionEvent.next] using hcounts.1
      hinactiveY := by
        unfold InfectionEvent.nextState
        rw [dif_neg he]
        simpa only [InfectionEvent.next] using hcounts.2 }

/-- Apply a positive ordered mixed activation witness. -/
noncomputable def infectionRevealPhysicalActivateTwoXY
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (p : InfectionInactiveXY s)
    (he : InfectionEvent.weight s.coarse.1 .activateTwoXY ≠ 0) :
    InfectionRevealPhysicalState n := by
  let op := infectionInactiveXYToOrdered p
  have hmul :
      s.coarse.1.active * s.coarse.1.ix *
          s.coarse.1.iy ≠ 0 := by
    simpa only [InfectionEvent.weight] using he
  have hix : s.coarse.1.ix ≠ 0 :=
    (Nat.mul_ne_zero_iff.mp
      (Nat.mul_ne_zero_iff.mp hmul).1).2
  have hiy : s.coarse.1.iy ≠ 0 :=
    (Nat.mul_ne_zero_iff.mp hmul).2
  have hx :
      s.inactive.xIds.card =
        (s.coarse.1.ix - 1) + 1 := by
    rw [s.hinactiveX]
    omega
  have hy :
      s.inactive.yIds.card =
        (s.coarse.1.iy - 1) + 1 := by
    rw [s.hinactiveY]
    omega
  have hcounts :
      (infectionRevealEraseTwo s.inactive op).xIds.card =
          s.coarse.1.ix - 1 ∧
        (infectionRevealEraseTwo s.inactive op).yIds.card =
          s.coarse.1.iy - 1 := by
    cases p with
    | inl p =>
        exact infectionRevealEraseTwo_counts_XY
          s.inactive op
          (infectionInactiveXToId_label p.1)
          (infectionInactiveYToId_label p.2)
          hx hy
    | inr p =>
        exact infectionRevealEraseTwo_counts_YX
          s.inactive op
          (infectionInactiveYToId_label p.1)
          (infectionInactiveXToId_label p.2)
          hx hy
  exact
    { coarse :=
        InfectionEvent.nextState s.coarse .activateTwoXY
      inactive := infectionRevealEraseTwo s.inactive op
      hinactiveCard := by
        have herase :=
          infectionRevealEraseTwo_card_add_two s.inactive op
        have hcard := s.hinactiveCard
        simp only [InfectionCfg.inactive] at hcard
        unfold InfectionEvent.nextState
        rw [dif_neg he]
        simp only [InfectionEvent.next, InfectionCfg.inactive]
        omega
      hinactiveX := by
        unfold InfectionEvent.nextState
        rw [dif_neg he]
        simpa only [InfectionEvent.next] using hcounts.1
      hinactiveY := by
        unfold InfectionEvent.nextState
        rw [dif_neg he]
        simpa only [InfectionEvent.next] using hcounts.2 }

/-- Apply a positive ordered `YY` activation witness. -/
noncomputable def infectionRevealPhysicalActivateTwoYY
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (p : InfectionInactiveYY s)
    (he : InfectionEvent.weight s.coarse.1 .activateTwoYY ≠ 0) :
    InfectionRevealPhysicalState n := by
  let op := infectionInactiveYYToOrdered p
  have hchoose : Nat.choose s.coarse.1.iy 2 ≠ 0 :=
    (Nat.mul_ne_zero_iff.mp (by
      simpa only [InfectionEvent.weight] using he)).2
  have hiy2 : 2 ≤ s.coarse.1.iy :=
    Nat.choose_ne_zero_iff.mp hchoose
  have hy :
      s.inactive.yIds.card =
        (s.coarse.1.iy - 2) + 2 := by
    rw [s.hinactiveY]
    omega
  have hfirst :
      s.inactive.initialLabel op.1.1.1 = .Y := by
    exact infectionInactiveYToId_label p.1.1
  have hsecond :
      s.inactive.initialLabel op.1.2.1 = .Y := by
    exact infectionInactiveYToId_label p.1.2
  have hcounts :=
    infectionRevealEraseTwo_counts_YY
      s.inactive op hfirst hsecond s.hinactiveX hy
  exact
    { coarse :=
        InfectionEvent.nextState s.coarse .activateTwoYY
      inactive := infectionRevealEraseTwo s.inactive op
      hinactiveCard := by
        have herase :=
          infectionRevealEraseTwo_card_add_two s.inactive op
        have hcard := s.hinactiveCard
        simp only [InfectionCfg.inactive] at hcard
        unfold InfectionEvent.nextState
        rw [dif_neg he]
        simp only [InfectionEvent.next, InfectionCfg.inactive]
        omega
      hinactiveX := by
        unfold InfectionEvent.nextState
        rw [dif_neg he]
        simpa only [InfectionEvent.next] using hcounts.1
      hinactiveY := by
        unfold InfectionEvent.nextState
        rw [dif_neg he]
        simpa only [InfectionEvent.next] using hcounts.2 }

/-- Apply the witness carried by an arbitrary positive semantic event. -/
noncomputable def infectionRevealPhysicalAfterPositive
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (e : InfectionEvent) (w : InfectionRevealWitness s e)
    (he : InfectionEvent.weight s.coarse.1 e ≠ 0) :
    InfectionRevealPhysicalState n :=
  match e with
  | .activeXXX =>
      infectionRevealPhysicalPreserve s .activeXXX he (by rfl) (by rfl)
  | .activeXXY =>
      infectionRevealPhysicalPreserve s .activeXXY he (by rfl) (by rfl)
  | .activeXYY =>
      infectionRevealPhysicalPreserve s .activeXYY he (by rfl) (by rfl)
  | .activeYYY =>
      infectionRevealPhysicalPreserve s .activeYYY he (by rfl) (by rfl)
  | .activateOneX =>
      infectionRevealPhysicalActivateOneX s w he
  | .activateOneY =>
      infectionRevealPhysicalActivateOneY s w he
  | .activateTwoXX =>
      infectionRevealPhysicalActivateTwoXX s w he
  | .activateTwoXY =>
      infectionRevealPhysicalActivateTwoXY s w he
  | .activateTwoYY =>
      infectionRevealPhysicalActivateTwoYY s w he
  | .inactiveOnly =>
      infectionRevealPhysicalPreserve s .inactiveOnly he (by rfl) (by rfl)

/-- Every positive refined update has the advertised coarse successor. -/
theorem infectionRevealPhysicalAfterPositive_forget
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (e : InfectionEvent) (w : InfectionRevealWitness s e)
    (he : InfectionEvent.weight s.coarse.1 e ≠ 0) :
    infectionRevealPhysicalForget
        (infectionRevealPhysicalAfterPositive s e w he) =
      InfectionEvent.nextState s.coarse e := by
  cases e <;>
    rfl

/-- Read the stored witness, with an arbitrary valid default on the
zero-probability `none` atom of a positive event. -/
noncomputable def InfectionRevealRecord.effectiveWitness
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (r : InfectionRevealRecord s)
    (he : InfectionEvent.weight s.coarse.1 r.event ≠ 0) :
    InfectionRevealWitness s r.event :=
  r.witness.getD
    (Classical.choice
      (infectionRevealWitness_nonempty_of_weight_ne_zero
        s r.event he))

/-- Total refined update associated with an event record. -/
noncomputable def InfectionRevealRecord.after
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (r : InfectionRevealRecord s) :
    InfectionRevealPhysicalState n :=
  if he : InfectionEvent.weight s.coarse.1 r.event = 0 then
    s
  else
    infectionRevealPhysicalAfterPositive s r.event (InfectionRevealRecord.effectiveWitness r he) he

/-- Every total record update projects to its stored coarse event update. -/
theorem InfectionRevealRecord.after_forget
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (r : InfectionRevealRecord s) :
    infectionRevealPhysicalForget (InfectionRevealRecord.after r) =
      InfectionEvent.nextState s.coarse r.event := by
  unfold InfectionRevealRecord.after
  by_cases he : InfectionEvent.weight s.coarse.1 r.event = 0
  · rw [dif_pos he]
    unfold InfectionEvent.nextState
    rw [dif_pos he]
    rfl
  · rw [dif_neg he]
    exact infectionRevealPhysicalAfterPositive_forget
      s r.event (InfectionRevealRecord.effectiveWitness r he) he

/-- One genuine physical infection step with inactive identities retained. -/
noncomputable def infectionRevealPhysicalStep
    (n : ℕ) (h3 : 3 ≤ n) :
    InfectionRevealPhysicalState n →
      PMF (InfectionRevealPhysicalState n) :=
  fun s =>
    (infectionRevealRecordPMF n h3 s).map InfectionRevealRecord.after

/-- The identity-refined physical step projects exactly to the original
infection count kernel. -/
theorem infectionRevealPhysicalStep_map_forget
    (n : ℕ) (h3 : 3 ≤ n)
    (s : InfectionRevealPhysicalState n) :
    (infectionRevealPhysicalStep n h3 s).map infectionRevealPhysicalForget =
      infectionStateStep n h3
        (infectionRevealPhysicalForget s) := by
  unfold infectionRevealPhysicalStep
  rw [PMF.map_comp]
  calc
    (infectionRevealRecordPMF n h3 s).map
        (infectionRevealPhysicalForget ∘ InfectionRevealRecord.after) =
        (infectionRevealRecordPMF n h3 s).map
          (InfectionEvent.nextState s.coarse ∘
            InfectionRevealRecord.event) := by
          congr 1
          funext r
          exact InfectionRevealRecord.after_forget r
    _ = ((infectionRevealRecordPMF n h3 s).map
          InfectionRevealRecord.event).map
            (InfectionEvent.nextState s.coarse) := by
          rw [PMF.map_comp]
    _ = (infectionEventPMF s.coarse.1
          (infectionRevealPhysicalTotalAtLeastThree n h3 s)).map
            (InfectionEvent.nextState s.coarse) := by
          rw [infectionRevealRecordPMF_map_event]
    _ = infectionStateStep n h3
          (infectionRevealPhysicalForget s) := by
          unfold infectionStateStep infectionRevealPhysicalForget
          congr

/-- Kernel-level form of the exact coarse projection. -/
theorem infectionRevealPhysicalStep_intertwines
    (n : ℕ) (h3 : 3 ≤ n) :
    Intertwines infectionRevealPhysicalForget
      (infectionRevealPhysicalStep n h3)
      (infectionStateStep n h3) :=
  infectionRevealPhysicalStep_map_forget n h3

/-- The exact coarse projection persists for every raw horizon. -/
theorem infectionRevealPhysicalStep_iter_map_forget
    (n : ℕ) (h3 : 3 ≤ n) (T : ℕ)
    (s : InfectionRevealPhysicalState n) :
    (iter (infectionRevealPhysicalStep n h3) T s).map
        infectionRevealPhysicalForget =
      iter (infectionStateStep n h3) T
        (infectionRevealPhysicalForget s) :=
  iter_map_of_intertwines
    (infectionRevealPhysicalStep_intertwines n h3) T s

end Tri

#print axioms Tri.InfectionRevealRecord.after_forget
#print axioms Tri.infectionRevealPhysicalAfterPositive_forget
#print axioms Tri.infectionRevealPhysicalStep_map_forget
#print axioms Tri.infectionRevealPhysicalStep_intertwines
#print axioms Tri.infectionRevealPhysicalStep_iter_map_forget
