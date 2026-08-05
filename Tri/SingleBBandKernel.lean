/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBDirection
import Tri.SingleBCreationTailY
import Tri.SingleBBudget
import Tri.BandReturn

/-!
# Single-B band kernel

The stopped Single-B band runs the oriented ledger chain from a fresh ledger and
freezes on the union of the corrected lower boundary, corrected upper boundary,
the `Y`-heavy creation-imbalance event, and the creation-budget boundary.
-/

namespace Tri

open scoped ENNReal

/-- The Single-B band frozen set, stated in subtraction-free corrected-level
form:

* lower: `(2x+b)+CY <= aLoΛ+CX`,
* upper: `hiΛ+CX <= (2x+b)+CY`,
* creation: `CreationBadY D H`,
* budget boundary: `H <= CX+CY`.
-/
def singleCreationBoundary {n : ℕ} (H : ℕ) (q : SingleLedger n) : Prop :=
  H ≤ q.cx + q.cy

instance {n H : ℕ} :
    DecidablePred (singleCreationBoundary (n := n) H) := fun _ =>
  inferInstanceAs (Decidable (_ ≤ _))

def SingleBandFrozen (n aLoΛ hiΛ D H : ℕ) (q : SingleLedger n) : Prop :=
  q.cfg.1.doubleLevel + q.cy ≤ aLoΛ + q.cx ∨
    hiΛ + q.cx ≤ q.cfg.1.doubleLevel + q.cy ∨
      CreationBadY D H q ∨ singleCreationBoundary H q

instance (n aLoΛ hiΛ D H : ℕ) :
    DecidablePred (SingleBandFrozen n aLoΛ hiΛ D H) := fun _ =>
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

/-- The stopped Single-B ledger kernel for one band. -/
noncomputable def singleBandStop (n : ℕ) (hn : 2 ≤ n)
    (aLoΛ hiΛ D H : ℕ) : SingleLedger n → PMF (SingleLedger n) :=
  freeze (SingleBandFrozen n aLoΛ hiΛ D H) (singleLedgerStep n hn)

/-- Characterization as the generic `freeze` combinator. -/
theorem singleBandStop_eq_freeze (n : ℕ) (hn : 2 ≤ n)
    (aLoΛ hiΛ D H : ℕ) :
    singleBandStop n hn aLoΛ hiΛ D H =
      freeze (SingleBandFrozen n aLoΛ hiΛ D H) (singleLedgerStep n hn) := rfl

/-- From a fresh ledger, the stopped Single-B band has creation count at most
the horizon.  Frozen steps hold the ledger fixed, so the raw one-step creation
budget survives the extra stopping boundary. -/
theorem singleBandStop_creation_budget_fresh {n T : ℕ} (hn : 2 ≤ n)
    (aLoΛ hiΛ D H : ℕ) (s : SingleState n) (z : SingleLedger n)
    (hz : iter (singleBandStop n hn aLoΛ hiΛ D H) T
      (⟨s, 0, 0, 0, 0⟩ : SingleLedger n) z ≠ 0) :
    z.cx + z.cy ≤ T := by
  simpa [singleBandStop] using
    (singleLedger_freeze_creation_budget (n := n) (T := T) hn
      (SingleBandFrozen n aLoΛ hiΛ D H) s z
      (by simpa [singleBandStop] using hz))

/-- From a fresh ledger, the stopped band never crosses past its creation
boundary: once `CX + CY` reaches `H`, the boundary freezes the chain. -/
theorem singleBandStop_creation_cap_fresh {n T : ℕ} (hn : 2 ≤ n)
    (aLoΛ hiΛ D H : ℕ) (s : SingleState n) (z : SingleLedger n)
    (hz : iter (singleBandStop n hn aLoΛ hiΛ D H) T
      (⟨s, 0, 0, 0, 0⟩ : SingleLedger n) z ≠ 0) :
    z.cx + z.cy ≤ H := by
  refine iter_support_closed (singleBandStop n hn aLoΛ hiΛ D H)
    (fun q : SingleLedger n => q.cx + q.cy ≤ H) ?_
    T (⟨s, 0, 0, 0, 0⟩ : SingleLedger n) z (by simp) hz
  intro q hq w hqw
  unfold singleBandStop freeze at hqw
  by_cases hB : SingleBandFrozen n aLoΛ hiΛ D H q
  · rw [if_pos hB, PMF.pure_apply] at hqw
    by_cases hwq : w = q
    · rwa [hwq]
    · simp [hwq] at hqw
  · rw [if_neg hB] at hqw
    have hnotBoundary : ¬ singleCreationBoundary H q := by
      intro hb
      exact hB (Or.inr (Or.inr (Or.inr hb)))
    have hlt : q.cx + q.cy < H := by
      unfold singleCreationBoundary at hnotBoundary
      exact Nat.lt_of_not_ge hnotBoundary
    have hstep := singleLedgerStep_creation_le hn q w hqw
    omega

/-- Forgetting ledger counters in one stopped step gives either the pure
physical state, if the ledger is frozen, or the ordinary Single-B state step. -/
theorem singleBandStop_map_cfg (n : ℕ) (hn : 2 ≤ n)
    (aLoΛ hiΛ D H : ℕ) (q : SingleLedger n) :
    (singleBandStop n hn aLoΛ hiΛ D H q).map SingleLedger.cfg =
      if SingleBandFrozen n aLoΛ hiΛ D H q then
        PMF.pure q.cfg
      else
        singleStateStep n hn q.cfg := by
  unfold singleBandStop freeze
  by_cases hB : SingleBandFrozen n aLoΛ hiΛ D H q
  · rw [if_pos hB, if_pos hB]
    exact PMF.pure_map SingleLedger.cfg q
  · rw [if_neg hB, if_neg hB]
    exact singleLedgerStep_map_cfg n hn q

/-- The physical Single-B state iterate is the pushforward of the raw oriented
ledger iterate. -/
theorem iter_singleStateStep_eq_map_singleLedgerStep
    (n : ℕ) (hn : 2 ≤ n) :
    ∀ (T : ℕ) (q : SingleLedger n),
      iter (singleStateStep n hn) T q.cfg =
        (iter (singleLedgerStep n hn) T q).map SingleLedger.cfg := by
  intro T
  induction T with
  | zero =>
      intro q
      rw [iter_zero, iter_zero, PMF.pure_map]
  | succ T ih =>
      intro q
      rw [iter_succ, iter_succ, ← singleLedgerStep_map_cfg n hn q, PMF.map_bind]
      rw [show (PMF.map SingleLedger.cfg (singleLedgerStep n hn q)).bind
            (iter (singleStateStep n hn) T)
          = (singleLedgerStep n hn q).bind
            (fun a => iter (singleStateStep n hn) T (SingleLedger.cfg a)) by
        simp only [PMF.map, PMF.bind_bind, Function.comp, PMF.pure_bind]]
      congr 1
      funext a
      exact ih a

/-- Failure mass for a physical state predicate is unchanged by forgetting the
raw ledger counters. -/
theorem singleState_failure_eq_ledger
    (n : ℕ) (hn : 2 ≤ n) (T : ℕ) (q₀ : SingleLedger n)
    (A : SingleState n → Prop) [DecidablePred A] :
    (∑' s, if A s then 0 else iter (singleStateStep n hn) T q₀.cfg s)
      =
    ∑' q, if A q.cfg then 0 else iter (singleLedgerStep n hn) T q₀ q := by
  rw [iter_singleStateStep_eq_map_singleLedgerStep n hn T q₀]
  set p := iter (singleLedgerStep n hn) T q₀
  let V : SingleState n → ℝ≥0∞ := fun s => if A s then 0 else 1
  calc
    (∑' s, if A s then 0 else (p.map SingleLedger.cfg) s)
        = expect (p.map SingleLedger.cfg) V := by
          unfold expect V
          apply tsum_congr
          intro s
          by_cases hs : A s <;> simp [hs]
    _ = expect p (fun q => V q.cfg) := by rw [expect_map]
    _ = ∑' q, if A q.cfg then 0 else p q := by
          unfold expect V
          apply tsum_congr
          intro q
          by_cases hq : A q.cfg <;> simp [hq]

/-- Generic upper-return transfer for the Single-B stopped ledger band.

The stopped kernel may freeze in successful upper states; the caller supplies a
uniform return bound `δ` for every frozen successful ledger state.  Lower and
creation frozen states that are already failures need no special handling.
-/
theorem singleBand_transfer_upper (n : ℕ) (hn : 2 ≤ n)
    (aLoΛ hiΛ D H T : ℕ) (q₀ : SingleLedger n)
    (A : SingleState n → Prop) [DecidablePred A] (δ : ℝ≥0∞)
    (hreturn : ∀ q : SingleLedger n,
      SingleBandFrozen n aLoΛ hiΛ D H q → A q.cfg → ∀ U : ℕ,
        (∑' s, if A s then 0 else iter (singleStateStep n hn) U q.cfg s) ≤ δ) :
    (∑' s, if A s then 0 else iter (singleStateStep n hn) T q₀.cfg s)
      ≤ (∑' q, if A q.cfg then 0 else
          iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀ q)
        + δ := by
  let B : SingleLedger n → Prop := SingleBandFrozen n aLoΛ hiΛ D H
  have hreturnLedger :
      ∀ q : SingleLedger n, B q → A q.cfg → ∀ U : ℕ,
        (∑' z, if A z.cfg then 0 else
            iter (singleLedgerStep n hn) U q z) ≤ δ := by
    intro q hB hA U
    rw [← singleState_failure_eq_ledger n hn U q A]
    exact hreturn q hB hA U
  have hraw :=
    failure_le_failure_freeze_add
      (B := B) (A := fun q : SingleLedger n => A q.cfg)
      (K := singleLedgerStep n hn) (δ := δ) hreturnLedger T q₀
  calc
    (∑' s, if A s then 0 else iter (singleStateStep n hn) T q₀.cfg s)
        = ∑' q, if A q.cfg then 0 else
            iter (singleLedgerStep n hn) T q₀ q :=
          singleState_failure_eq_ledger n hn T q₀ A
    _ ≤ (∑' q, if A q.cfg then 0 else
            iter (freeze B (singleLedgerStep n hn)) T q₀ q) + δ := hraw
    _ = (∑' q, if A q.cfg then 0 else
            iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀ q) + δ := by
          simp only [singleBandStop, B]

/-- A small physical target-failure wrapper: if a separate Feller/ruin engine
controls returns to `returnLo`, then terminal failure of any target whose
failure implies `x <= returnLo` is bounded by the same return term. -/
theorem singleState_upper_target_failure_of_ruin
    (n : ℕ) (hn : 2 ≤ n) (returnLo bHi k T : ℕ)
    (s : SingleState n)
    (A : SingleState n → Prop) [DecidablePred A]
    (hfailure : ∀ z, ¬ A z → z.1.x ≤ returnLo)
    (hruin : ∀ U : ℕ,
      hitProb (fun z : SingleState n => z.1.x ≤ returnLo)
        (singleStateStep n hn) U s
        ≤ ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k) :
    (∑' z, if A z then 0 else iter (singleStateStep n hn) T s z)
      ≤ ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k := by
  calc
    (∑' z, if A z then 0 else iter (singleStateStep n hn) T s z)
        ≤ ∑' z, if returnLo < z.1.x then 0 else
            iter (singleStateStep n hn) T s z := by
          refine ENNReal.tsum_le_tsum fun z => ?_
          by_cases hA : A z
          · simp [hA]
          · have hz := hfailure z hA
            have hnlt : ¬ returnLo < z.1.x := Nat.not_lt.mpr hz
            simp [hA, hnlt]
    _ ≤ ∑' z, if returnLo < z.1.x then 0 else
            iter (freeze (fun z : SingleState n => z.1.x ≤ returnLo)
              (singleStateStep n hn)) T s z :=
          failure_le_failure_freeze
            (B := fun z : SingleState n => z.1.x ≤ returnLo)
            (A := fun z : SingleState n => returnLo < z.1.x)
            (by omega) T s
    _ = hitProb (fun z : SingleState n => z.1.x ≤ returnLo)
          (singleStateStep n hn) T s := by
          unfold hitProb expect ind
          apply tsum_congr
          intro z
          by_cases hz : z.1.x ≤ returnLo
          · have hnlt : ¬ returnLo < z.1.x := Nat.not_lt.mpr hz
            simp [hz, hnlt]
          · have hlt : returnLo < z.1.x := Nat.lt_of_not_ge hz
            simp [hz, hlt]
    _ ≤ ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k := hruin T

/-- Transfer with an explicitly supplied physical return/ruin bound for upper
frozen states. -/
theorem singleBand_transfer_upper_of_ruin (n : ℕ) (hn : 2 ≤ n)
    (aLoΛ hiΛ D H T returnLo bHi k : ℕ) (q₀ : SingleLedger n)
    (A : SingleState n → Prop) [DecidablePred A]
    (hfailure : ∀ z, ¬ A z → z.1.x ≤ returnLo)
    (hruin : ∀ q : SingleLedger n,
      SingleBandFrozen n aLoΛ hiΛ D H q → A q.cfg → ∀ U : ℕ,
        hitProb (fun z : SingleState n => z.1.x ≤ returnLo)
          (singleStateStep n hn) U q.cfg
          ≤ ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k) :
    (∑' s, if A s then 0 else iter (singleStateStep n hn) T q₀.cfg s)
      ≤ (∑' q, if A q.cfg then 0 else
          iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀ q)
        + ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k := by
  exact singleBand_transfer_upper n hn aLoΛ hiΛ D H T q₀ A
    (((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k)
    (fun q hB hA U =>
      singleState_upper_target_failure_of_ruin n hn returnLo bHi k U q.cfg A
        hfailure (hruin q hB hA))

section Inhabitation

example :
    ∃ q : SingleLedger 4, ¬ SingleBandFrozen 4 3 6 2 5 q := by
  refine ⟨⟨⟨⟨2, 1, 1⟩, by norm_num [BiCfg.DoubleInv]⟩,
      0, 0, 0, 0⟩, ?_⟩
  norm_num [SingleBandFrozen, BiCfg.doubleLevel, CreationBadY, singleCreationBoundary]

example :
    ∃ q : SingleLedger 4, SingleBandFrozen 4 1 8 2 5 q := by
  refine ⟨⟨⟨⟨0, 3, 1⟩, by norm_num [BiCfg.DoubleInv]⟩,
      0, 0, 0, 0⟩, ?_⟩
  norm_num [SingleBandFrozen, BiCfg.doubleLevel, singleCreationBoundary]

example :
    ∃ q : SingleLedger 4, SingleBandFrozen 4 1 8 2 5 q := by
  refine ⟨⟨⟨⟨4, 0, 0⟩, by norm_num [BiCfg.DoubleInv]⟩,
      0, 0, 0, 0⟩, ?_⟩
  norm_num [SingleBandFrozen, BiCfg.doubleLevel, singleCreationBoundary]

example :
    ∃ q : SingleLedger 4, SingleBandFrozen 4 1 8 2 2 q := by
  refine ⟨⟨⟨⟨2, 1, 1⟩, by norm_num [BiCfg.DoubleInv]⟩,
      0, 2, 0, 0⟩, ?_⟩
  norm_num [SingleBandFrozen, BiCfg.doubleLevel, CreationBadY, singleCreationBoundary]

end Inhabitation

end Tri

#print axioms Tri.singleBandStop_creation_budget_fresh
#print axioms Tri.singleBandStop_creation_cap_fresh
#print axioms Tri.singleBandStop_eq_freeze
#print axioms Tri.singleBandStop_map_cfg
#print axioms Tri.iter_singleStateStep_eq_map_singleLedgerStep
#print axioms Tri.singleState_failure_eq_ledger
#print axioms Tri.singleBand_transfer_upper
#print axioms Tri.singleState_upper_target_failure_of_ruin
#print axioms Tri.singleBand_transfer_upper_of_ruin
