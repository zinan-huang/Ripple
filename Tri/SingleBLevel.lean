/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBTrace

/-!
# Single-B corrected level: the orientation ledger

## Why the Double-B level does not port

Double-B runs on the level `2x + b`, and the whole direction/clock engine
rests on one fact: **the level moves only at resolution events.**  For
Single-B that is false for every level built from the physical counts alone.
The obstruction is the creation pair: `X+Y → X+B` and `X+Y → Y+B` are two
distinct events with the SAME weight `x*y`, and they move `(x, y, b)` in two
different directions.  Any function of `(x, y, b)` therefore moves at
creations, so no such function can be the Double-B level.

This was established by a dispatched audit that refuted an earlier and easier
reading ("the blank cancels, so Single-B is a verbatim port").  The blank does
cancel — that part was right — but the level needs history.

## The fix: two monotone corrected coordinates

Rather than a signed corrected level `(2x + b) − CX + CY`, which would need
ℕ-subtraction in every statement, carry the orientation counters and use

```text
LX = x + CY        LY = y + CX
```

Both are ℕ-valued and both are *monotone along every trajectory*, because the
exact invariants

```text
x + CY = x₀ + RX          y + CX = y₀ + RY
```

hold on the support.  Read them right-to-left: `LX` counts `x₀` plus the
number of `X`-resolutions and NOTHING else; `LY` counts `y₀` plus the number
of `Y`-resolutions and nothing else.  Creations move neither.  That is exactly
the Double-B property — "the level moves only at resolutions" — recovered on
the corrected coordinates.

The signed corrected gap is `LX − LY`, and every statement uses it in the
subtraction-free form `LY + d ≤ LX`.

## Fuel coefficient

Double-B's pathwise fuel relation carries a factor 2, inherited from the level
doubling.  Here `CorrectedY` says `CX + y = y₀ + RY` on the nose, and
`RY ≤ RX + RY`, so with the fuel taken to be the minority-side creation ledger
`CX` the relation is

```text
fuel + y = y₀ + RY ≤ y₀ + resolve
```

with coefficient **one**, not two.

## What is still not a port

Recovering the PHYSICAL gap from the corrected gap leaves the signed creation
imbalance `CX − CY`, which is a fair ±1 walk on the creation events and needs
its own concentration bound.  That is the one genuinely new piece; everything
above it ports.
-/

namespace Tri

open scoped ENNReal

/-- Single-B state augmented with the four ORIENTED event counters.  The
existing `SingleTrace` carries only the aggregate `productive`/`resolve`,
which is enough for the blank ledger but not for the corrected level: the two
creations are indistinguishable there, and telling them apart is the whole
point. -/
structure SingleLedger (n : ℕ) where
  cfg : SingleState n
  /-- number of `X+Y → X+B` creations -/
  cx : ℕ
  /-- number of `X+Y → Y+B` creations -/
  cy : ℕ
  /-- number of `X+B → X+X` resolutions -/
  rx : ℕ
  /-- number of `Y+B → Y+Y` resolutions -/
  ry : ℕ

namespace SingleComp

def cxInc : SingleComp → ℕ
  | .xyToX => 1
  | _ => 0

def cyInc : SingleComp → ℕ
  | .xyToY => 1
  | _ => 0

def rxInc : SingleComp → ℕ
  | .xb => 1
  | _ => 0

def ryInc : SingleComp → ℕ
  | .yb => 1
  | _ => 0

/-- Guarded oriented update; zero-weight labels leave the ledger fixed. -/
noncomputable def nextSingleLedger
    {n : ℕ} (q : SingleLedger n) (k : SingleComp) : SingleLedger n :=
  if hk :
      SingleComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k = 0 then
    q
  else
    { cfg :=
        ⟨SingleComp.next q.cfg.1 k,
          SingleComp.next_doubleInv n q.cfg.1 k q.cfg.2 hk⟩
      cx := q.cx + k.cxInc
      cy := q.cy + k.cyInc
      rx := q.rx + k.rxInc
      ry := q.ry + k.ryInc }

end SingleComp

/-- One oriented Single-B interaction. -/
noncomputable def singleLedgerStep
    (n : ℕ) (hn : 2 ≤ n) (q : SingleLedger n) : PMF (SingleLedger n) :=
  (singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
    have h := q.cfg.2
    simp only [BiCfg.DoubleInv] at h
    omega)).map (SingleComp.nextSingleLedger q)

/-- **The corrected X level.**  `x + CY = x₀ + RX`: the corrected level is
`x₀` plus the number of `X`-resolutions, and creations do not move it. -/
def SingleLedger.CorrectedX {n : ℕ} (x₀ : ℕ) (q : SingleLedger n) : Prop :=
  q.cfg.1.x + q.cy = x₀ + q.rx

/-- **The corrected Y level.**  `y + CX = y₀ + RY`, symmetrically. -/
def SingleLedger.CorrectedY {n : ℕ} (y₀ : ℕ) (q : SingleLedger n) : Prop :=
  q.cfg.1.y + q.cx = y₀ + q.ry

instance {n x₀ : ℕ} : DecidablePred (SingleLedger.CorrectedX (n := n) x₀) :=
  fun _ => inferInstanceAs (Decidable (_ = _))

instance {n y₀ : ℕ} : DecidablePred (SingleLedger.CorrectedY (n := n) y₀) :=
  fun _ => inferInstanceAs (Decidable (_ = _))

theorem SingleLedger.initial_correctedX {n : ℕ} (s : SingleState n) :
    SingleLedger.CorrectedX s.1.x ⟨s, 0, 0, 0, 0⟩ := by
  simp [SingleLedger.CorrectedX]

theorem SingleLedger.initial_correctedY {n : ℕ} (s : SingleState n) :
    SingleLedger.CorrectedY s.1.y ⟨s, 0, 0, 0, 0⟩ := by
  simp [SingleLedger.CorrectedY]

/-- The corrected X level survives one oriented event.

The four live cases are the content.  `xyToX` leaves both `x` and `CY` alone;
`xyToY` drops `x` by one and raises `CY` by one, and the weight `x*y ≠ 0`
supplies the `1 ≤ x` that makes the ℕ-subtraction in `next` exact; `xb` raises
both `x` and `RX`; `yb` touches neither side. -/
theorem SingleComp.nextSingleLedger_correctedX
    {n x₀ : ℕ} (q : SingleLedger n) (k : SingleComp)
    (hq : q.CorrectedX x₀)
    (hw : SingleComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k ≠ 0) :
    (SingleComp.nextSingleLedger q k).CorrectedX x₀ := by
  unfold SingleComp.nextSingleLedger
  rw [dif_neg hw]
  simp only [SingleLedger.CorrectedX] at hq ⊢
  cases k <;>
    simp only [SingleComp.cyInc, SingleComp.rxInc,
      SingleComp.next, SingleComp.weight] at hw ⊢ <;>
    first
    | omega
    | (rw [Nat.mul_ne_zero_iff] at hw; omega)

/-- The corrected `X` coordinate is an exact one-step invariant: if it is false
before a guarded event, it is still false afterwards. -/
theorem SingleComp.nextSingleLedger_not_correctedX
    {n x₀ : ℕ} (q : SingleLedger n) (k : SingleComp)
    (hq : ¬ q.CorrectedX x₀) :
    ¬ (SingleComp.nextSingleLedger q k).CorrectedX x₀ := by
  intro hz
  unfold SingleComp.nextSingleLedger at hz
  by_cases hw : SingleComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k = 0
  · rw [dif_pos hw] at hz
    exact hq hz
  · rw [dif_neg hw] at hz
    apply hq
    rcases q with ⟨⟨⟨x, y, b⟩, hinv⟩, cx, cy, rx, ry⟩
    simp only [SingleLedger.CorrectedX, SingleComp.next, SingleComp.weight,
      SingleComp.cyInc, SingleComp.rxInc] at hz hw ⊢
    cases k <;> simp only [SingleComp.next, SingleComp.weight,
      SingleComp.cyInc, SingleComp.rxInc] at hz hw ⊢ <;>
      first
      | omega
      | (have hxy := Nat.mul_ne_zero_iff.mp hw; omega)

/-- The corrected Y level survives one oriented event. -/
theorem SingleComp.nextSingleLedger_correctedY
    {n y₀ : ℕ} (q : SingleLedger n) (k : SingleComp)
    (hq : q.CorrectedY y₀)
    (hw : SingleComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k ≠ 0) :
    (SingleComp.nextSingleLedger q k).CorrectedY y₀ := by
  unfold SingleComp.nextSingleLedger
  rw [dif_neg hw]
  simp only [SingleLedger.CorrectedY] at hq ⊢
  cases k <;>
    simp only [SingleComp.cxInc, SingleComp.ryInc,
      SingleComp.next, SingleComp.weight] at hw ⊢ <;>
    first
    | omega
    | (rw [Nat.mul_ne_zero_iff] at hw; omega)

theorem singleLedgerStep_correctedX_of_apply_ne_zero
    {n x₀ : ℕ} (hn : 2 ≤ n) (q : SingleLedger n)
    (hq : q.CorrectedX x₀) (z : SingleLedger n)
    (hqz : singleLedgerStep n hn q z ≠ 0) :
    z.CorrectedX x₀ := by
  unfold singleLedgerStep at hqz
  rw [PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at hqz
  push Not at hqz
  obtain ⟨k, hk⟩ := hqz
  split_ifs at hk with hzk
  · have hw :
        SingleComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k ≠ 0 :=
      fun hw => hk (singleCompPMF_zero_of_weight_zero hw)
    rw [hzk]
    exact SingleComp.nextSingleLedger_correctedX q k hq hw
  · exact absurd rfl hk

theorem singleLedgerStep_not_correctedX_of_apply_ne_zero
    {n x₀ : ℕ} (hn : 2 ≤ n) (q : SingleLedger n)
    (hq : ¬ q.CorrectedX x₀) (z : SingleLedger n)
    (hqz : singleLedgerStep n hn q z ≠ 0) :
    ¬ z.CorrectedX x₀ := by
  unfold singleLedgerStep at hqz
  rw [PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at hqz
  push Not at hqz
  obtain ⟨k, hk⟩ := hqz
  split_ifs at hk with hzk
  · rw [hzk]
    exact SingleComp.nextSingleLedger_not_correctedX q k hq
  · exact absurd rfl hk

theorem singleLedgerStep_correctedY_of_apply_ne_zero
    {n y₀ : ℕ} (hn : 2 ≤ n) (q : SingleLedger n)
    (hq : q.CorrectedY y₀) (z : SingleLedger n)
    (hqz : singleLedgerStep n hn q z ≠ 0) :
    z.CorrectedY y₀ := by
  unfold singleLedgerStep at hqz
  rw [PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at hqz
  push Not at hqz
  obtain ⟨k, hk⟩ := hqz
  split_ifs at hk with hzk
  · have hw :
        SingleComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k ≠ 0 :=
      fun hw => hk (singleCompPMF_zero_of_weight_zero hw)
    rw [hzk]
    exact SingleComp.nextSingleLedger_correctedY q k hq hw
  · exact absurd rfl hk

/-- **The corrected X level holds along every finite trajectory.** -/
theorem singleLedger_iter_correctedX
    {n x₀ T : ℕ} (hn : 2 ≤ n) (q z : SingleLedger n)
    (hq : q.CorrectedX x₀)
    (hz : iter (singleLedgerStep n hn) T q z ≠ 0) :
    z.CorrectedX x₀ :=
  iter_support_closed
    (singleLedgerStep n hn) (SingleLedger.CorrectedX x₀)
    (fun a ha z haz =>
      singleLedgerStep_correctedX_of_apply_ne_zero hn a ha z haz)
    T q z hq hz

/-- **The corrected Y level holds along every finite trajectory.** -/
theorem singleLedger_iter_correctedY
    {n y₀ T : ℕ} (hn : 2 ≤ n) (q z : SingleLedger n)
    (hq : q.CorrectedY y₀)
    (hz : iter (singleLedgerStep n hn) T q z ≠ 0) :
    z.CorrectedY y₀ :=
  iter_support_closed
    (singleLedgerStep n hn) (SingleLedger.CorrectedY y₀)
    (fun a ha z haz =>
      singleLedgerStep_correctedY_of_apply_ne_zero hn a ha z haz)
    T q z hq hz

/-- **The Double-B property, recovered.**  On the corrected coordinates the
level is a function of the RESOLUTION counters alone — creations are invisible
to it.  This is the exact statement that fails for every level built from the
physical counts, and it is what lets the Double-B direction/clock engine port.

Stated as the conjunction of the two invariants, which is how a caller uses
it: the corrected gap `LY + d ≤ LX` is `y₀ + RY + d ≤ x₀ + RX`. -/
theorem singleLedger_level_moves_only_at_resolution
    {n x₀ y₀ : ℕ} (q : SingleLedger n)
    (hx : q.CorrectedX x₀) (hy : q.CorrectedY y₀) :
    q.cfg.1.x + q.cy = x₀ + q.rx ∧ q.cfg.1.y + q.cx = y₀ + q.ry :=
  ⟨hx, hy⟩

/-- **The corrected gap in subtraction-free form.**  A corrected-level
advantage `d` is exactly an excess of `X`-resolutions over `Y`-resolutions,
offset by the initial counts. -/
theorem singleLedger_corrected_gap
    {n x₀ y₀ d : ℕ} (q : SingleLedger n)
    (hx : q.CorrectedX x₀) (hy : q.CorrectedY y₀)
    (hgap : y₀ + q.ry + d ≤ x₀ + q.rx) :
    q.cfg.1.y + q.cx + d ≤ q.cfg.1.x + q.cy := by
  simp only [SingleLedger.CorrectedX] at hx
  simp only [SingleLedger.CorrectedY] at hy
  omega

/-- **The fuel relation, with coefficient one.**  Double-B's carries a factor
`2`, inherited from its level doubling.  Single-B's is exact on the nose:
taking the fuel to be the minority-side creation ledger `CX`,

`fuel + y = y₀ + RY ≤ y₀ + resolve`.

This is the one place where Single-B is quantitatively BETTER than Double-B,
and it is a direct consequence of the corrected coordinates being un-doubled. -/
theorem singleLedger_fuel
    {n y₀ : ℕ} (q : SingleLedger n) (hy : q.CorrectedY y₀) :
    q.cx + q.cfg.1.y ≤ y₀ + (q.rx + q.ry) := by
  simp only [SingleLedger.CorrectedY] at hy
  omega

/-- Forgetting the oriented counters recovers the invariant Single-B step. -/
theorem singleLedgerStep_map_cfg
    (n : ℕ) (hn : 2 ≤ n) (q : SingleLedger n) :
    (singleLedgerStep n hn q).map SingleLedger.cfg =
      singleStateStep n hn q.cfg := by
  unfold singleLedgerStep singleStateStep
  rw [PMF.map_comp]
  apply PMF.map_change_on_zero_mass
  intro k hkdiff
  unfold Function.comp SingleComp.nextSingleLedger
    SingleComp.nextSingleState at hkdiff
  split_ifs at hkdiff with hk
  · exact singleCompPMF_zero_of_weight_zero hk
  · exact absurd rfl hkdiff

end Tri

#print axioms Tri.SingleComp.nextSingleLedger_correctedX
#print axioms Tri.SingleComp.nextSingleLedger_not_correctedX
#print axioms Tri.SingleComp.nextSingleLedger_correctedY
#print axioms Tri.singleLedger_iter_correctedX
#print axioms Tri.singleLedgerStep_not_correctedX_of_apply_ne_zero
#print axioms Tri.singleLedger_iter_correctedY
#print axioms Tri.singleLedger_level_moves_only_at_resolution
#print axioms Tri.singleLedger_corrected_gap
#print axioms Tri.singleLedger_fuel
#print axioms Tri.singleLedgerStep_map_cfg
