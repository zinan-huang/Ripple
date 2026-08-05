/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiStrictBias
import Tri.Phase3Productive

/-!
# Two-channel pairwise lock-in ledger

For a fixed ordered pair `X,Y`, the ledger records two signed adverse nets:

* `directNet`: direct `Y`-wins-`X` events minus direct `X`-wins-`Y` events;
* `thirdNet`: adverse third-party unit moves minus favorable third-party moves.

A direct event changes the physical pair gap by two, whereas a third-party event
changes it by one.  Therefore

`pairGap cfg X Y + 2 * directNet + thirdNet`

is exactly conserved.  The later lock-in tail may bound the two counters with
separate geometric potentials and combine them by a union bound.
-/

namespace Tri.Multi

noncomputable section

variable {m n : ℕ}

/-- A physical multi-species configuration with separate signed adverse nets
for the direct and third-party channels of one fixed pair. -/
structure PairLedger (m n : ℕ) where
  cfg : Config m n
  directNet : ℤ
  thirdNet : ℤ

/-- Start a pair ledger with no accumulated traffic. -/
def PairLedger.initial (c : Config m n) : PairLedger m n :=
  ⟨c, 0, 0⟩

/-- Physical pair-gap increment contributed by a direct `X/Y` firing.  Every
other sample contributes zero to this channel. -/
noncomputable def sampleDirectPairDelta
    {c : Config m n} (t : TripleSample c)
    (X Y : Species m) : ℤ :=
  match classify t with
  | none => 0
  | some p =>
      if (p.1.1 = X ∧ p.1.2 = Y) ∨
          (p.1.1 = Y ∧ p.1.2 = X) then
        directedPairDelta p.1.1 p.1.2 X Y
      else
        0

/-- Signed adverse direct increment.  An `X` win against `Y` contributes `-1`;
a `Y` win against `X` contributes `+1`; all other samples contribute zero. -/
noncomputable def directNetInc
    {c : Config m n} (t : TripleSample c)
    (X Y : Species m) : ℤ :=
  match classify t with
  | none => 0
  | some p =>
      if p.1.1 = X ∧ p.1.2 = Y then
        -1
      else if p.1.1 = Y ∧ p.1.2 = X then
        1
      else
        0

/-- The residual physical pair-gap increment after removing the direct
size-two channel. -/
noncomputable def sampleThirdPairDelta
    {c : Config m n} (t : TripleSample c)
    (X Y : Species m) : ℤ :=
  samplePairDelta t X Y - sampleDirectPairDelta t X Y

/-- Signed adverse third-party increment: the negative of the residual
physical unit increment. -/
noncomputable def thirdNetInc
    {c : Config m n} (t : TripleSample c)
    (X Y : Species m) : ℤ :=
  -sampleThirdPairDelta t X Y

/-- **Direct-channel conservation.**  The direct physical gap increment is
cancelled exactly by twice the adverse direct-net increment. -/
theorem sampleDirectPairDelta_add_two_mul_directNetInc
    {c : Config m n} (t : TripleSample c)
    (X Y : Species m) (hXY : X ≠ Y) :
    sampleDirectPairDelta t X Y +
        2 * directNetInc t X Y = 0 := by
  classical
  unfold sampleDirectPairDelta directNetInc
  cases hclass : classify t with
  | none =>
      simp only [hclass]
      norm_num
  | some p =>
      simp only [hclass]
      by_cases hup : p.1.1 = X ∧ p.1.2 = Y
      · rw [if_pos (Or.inl hup), if_pos hup]
        rw [directedPairDelta_direct_up hup.1 hup.2 hXY]
        norm_num
      · by_cases hdown : p.1.1 = Y ∧ p.1.2 = X
        · rw [if_pos (Or.inr hdown), if_neg hup, if_pos hdown]
          rw [directedPairDelta_direct_down hdown.1 hdown.2 hXY]
          norm_num
        · have hnot :
              ¬ ((p.1.1 = X ∧ p.1.2 = Y) ∨
                (p.1.1 = Y ∧ p.1.2 = X)) := by
            intro h
            rcases h with h | h
            · exact hup h
            · exact hdown h
          rw [if_neg hnot, if_neg hup, if_neg hdown]
          norm_num

/-- **Third-party-channel conservation.**  The residual physical gap increment
is cancelled exactly by the adverse third-party-net increment. -/
theorem sampleThirdPairDelta_add_thirdNetInc
    {c : Config m n} (t : TripleSample c)
    (X Y : Species m) :
    sampleThirdPairDelta t X Y + thirdNetInc t X Y = 0 := by
  unfold thirdNetInc
  ring

/-- The physical pair-gap increment is the sum of its direct and third-party
channel contributions. -/
theorem samplePairDelta_eq_direct_add_third
    {c : Config m n} (t : TripleSample c)
    (X Y : Species m) :
    samplePairDelta t X Y =
      sampleDirectPairDelta t X Y + sampleThirdPairDelta t X Y := by
  unfold sampleThirdPairDelta
  ring

/-- Guard-free ledger update driven by one physical triple sample. -/
noncomputable def pairLedgerNext
    (X Y : Species m) (q : PairLedger m n)
    (t : TripleSample q.cfg) : PairLedger m n :=
  { cfg := sampleNext q.cfg t
    directNet := q.directNet + directNetInc t X Y
    thirdNet := q.thirdNet + thirdNetInc t X Y }

/-- One raw interaction of the two-counter pair ledger. -/
noncomputable def pairLedgerStep
    (h3 : 3 ≤ n) (X Y : Species m)
    (q : PairLedger m n) : PMF (PairLedger m n) :=
  (triplePMF q.cfg h3).map (pairLedgerNext X Y q)

/-- Forgetting both counters recovers the physical multi-species kernel
exactly. -/
theorem pairLedgerStep_map_cfg
    (h3 : 3 ≤ n) (X Y : Species m)
    (q : PairLedger m n) :
    (pairLedgerStep h3 X Y q).map (fun r => r.cfg) =
      multiStep q.cfg h3 := by
  unfold pairLedgerStep multiStep
  rw [PMF.map_comp]
  apply congrArg (fun f => PMF.map f (triplePMF q.cfg h3))
  funext t
  rfl

/-- The conserved corrected pair gap. -/
def PairLedger.lockValue
    (q : PairLedger m n) (X Y : Species m) : ℤ :=
  pairGap q.cfg X Y + 2 * q.directNet + q.thirdNet

@[simp] theorem PairLedger.initial_lockValue
    (c : Config m n) (X Y : Species m) :
    (PairLedger.initial c).lockValue X Y = pairGap c X Y := by
  simp [PairLedger.initial, PairLedger.lockValue]

/-- One sampled ledger update preserves the corrected pair gap exactly. -/
theorem pairLedgerNext_lockValue
    (X Y : Species m) (hXY : X ≠ Y)
    (q : PairLedger m n) (t : TripleSample q.cfg) :
    (pairLedgerNext X Y q t).lockValue X Y = q.lockValue X Y := by
  change
    pairGap (sampleNext q.cfg t) X Y +
        2 * (q.directNet + directNetInc t X Y) +
        (q.thirdNet + thirdNetInc t X Y) =
      pairGap q.cfg X Y + 2 * q.directNet + q.thirdNet
  rw [pairGap_sampleNext]
  have hd :=
    sampleDirectPairDelta_add_two_mul_directNetInc t X Y hXY
  have ht := sampleThirdPairDelta_add_thirdNetInc t X Y
  calc
    pairGap q.cfg X Y + samplePairDelta t X Y +
          2 * (q.directNet + directNetInc t X Y) +
          (q.thirdNet + thirdNetInc t X Y) =
        pairGap q.cfg X Y + 2 * q.directNet + q.thirdNet +
          ((sampleDirectPairDelta t X Y +
              2 * directNetInc t X Y) +
            (sampleThirdPairDelta t X Y + thirdNetInc t X Y)) := by
      rw [samplePairDelta_eq_direct_add_third t X Y]
      ring
    _ = pairGap q.cfg X Y + 2 * q.directNet + q.thirdNet := by
      rw [hd, ht]
      ring

/-- Every positive-mass one-step successor preserves the corrected pair gap. -/
theorem pairLedgerStep_lockValue_of_apply_ne_zero
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (q z : PairLedger m n)
    (hqz : pairLedgerStep h3 X Y q z ≠ 0) :
    z.lockValue X Y = q.lockValue X Y := by
  classical
  unfold pairLedgerStep at hqz
  rw [PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at hqz
  push Not at hqz
  obtain ⟨t, ht⟩ := hqz
  split_ifs at ht with hzt
  · rw [hzt]
    exact pairLedgerNext_lockValue X Y hXY q t
  · exact absurd rfl ht

/-- The corrected pair gap is conserved along every finite ledger trajectory. -/
theorem pairLedger_iter_lockValue
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (T : ℕ) (q z : PairLedger m n)
    (hz : iter (pairLedgerStep h3 X Y) T q z ≠ 0) :
    z.lockValue X Y = q.lockValue X Y :=
  iter_support_closed
    (pairLedgerStep h3 X Y)
    (fun r => r.lockValue X Y = q.lockValue X Y)
    (fun a ha b hab =>
      (pairLedgerStep_lockValue_of_apply_ne_zero
        h3 X Y hXY a b hab).trans ha)
    T q z rfl hz

/-- Starting from zero counters, the physical gap loss is exactly the weighted
sum of the two adverse nets. -/
theorem pairLedger_iter_from_initial
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (T : ℕ) (c : Config m n) (z : PairLedger m n)
    (hz :
      iter (pairLedgerStep h3 X Y) T (PairLedger.initial c) z ≠ 0) :
    pairGap z.cfg X Y + 2 * z.directNet + z.thirdNet =
      pairGap c X Y := by
  have h := pairLedger_iter_lockValue
    h3 X Y hXY T (PairLedger.initial c) z hz
  simpa [PairLedger.lockValue, PairLedger.initial] using h

end

end Tri.Multi
