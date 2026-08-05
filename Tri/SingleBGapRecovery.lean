/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBLevel
import Tri.Theorem2

/-!
# Recovering physical Single-B facts from the corrected ledger

`Tri.SingleBLevel` already provides the support identity
`singleLedger_corrected_gap`.  This file packages the downstream arithmetic
exports: a corrected gap plus a non-`Y`-heavy creation imbalance gives a
physical gap, a corrected co-level gives a physical co-level bound, and a large
corrected gap exports physical all-`X` consensus.

The corrected doubled level is represented subtraction-free as the relation

```text
  (2x+b) + CY = Lambda + CX,
```

which carries `Lambda = 2x+b+CY-CX`.  The co-level mirror is represented by

```text
  (2y+b) + CX = Xi + CY.
```
-/

namespace Tri

open scoped ENNReal

namespace SingleLedger

/-- Corrected doubled `X` level, carried as an additive relation:
`Lambda = (2x+b)+CY-CX`. -/
def CorrectedLevel {n : ℕ} (Lambda : ℕ) (q : SingleLedger n) : Prop :=
  q.cfg.1.doubleLevel + q.cy = Lambda + q.cx

/-- Corrected doubled `Y` co-level, carried as an additive relation:
`Xi = (2y+b)+CX-CY`. -/
def CorrectedCoLevel {n : ℕ} (Xi : ℕ) (q : SingleLedger n) : Prop :=
  q.cfg.1.doubleCoLevel + q.cx = Xi + q.cy

end SingleLedger

/-- Recover a physical `X` gap from a corrected gap and a bound on the
`Y`-heavy creation imbalance. -/
theorem single_gap_recover {n G D : ℕ} (q : SingleLedger n)
    (hgap : q.cfg.1.y + q.cx + G ≤ q.cfg.1.x + q.cy)
    (hbal : q.cy ≤ q.cx + D) :
    G + q.cfg.1.y ≤ q.cfg.1.x + D := by
  omega

/-- Recover a physical co-level bound from the corrected co-level and the same
creation-imbalance bound. -/
theorem single_co_recover {n Xi D : ℕ} (q : SingleLedger n)
    (hco : q.CorrectedCoLevel Xi)
    (hbal : q.cy ≤ q.cx + D) :
    q.cfg.1.doubleCoLevel ≤ Xi + D := by
  simp only [SingleLedger.CorrectedCoLevel] at hco
  omega

/-- A corrected gap of at least `n+D`, together with imbalance at most `D`,
forces physical all-`X` consensus. -/
theorem single_consensus_export {n D : ℕ} (q : SingleLedger n)
    (hgap : q.cfg.1.y + q.cx + (n + D) ≤ q.cfg.1.x + q.cy)
    (hbal : q.cy ≤ q.cx + D) :
    BiXConsensus n q.cfg.1 := by
  have hphys := single_gap_recover (G := n + D) (D := D) q hgap hbal
  have hinv := q.cfg.2
  simp only [BiCfg.DoubleInv] at hinv
  simp only [BiXConsensus]
  omega

namespace SingleComp

/-- The `XX` event leaves the corrected doubled level unchanged. -/
theorem nextSingleLedger_correctedLevel_xx {n Lambda : ℕ}
    (q : SingleLedger n) (hL : q.CorrectedLevel Lambda) :
    (SingleComp.nextSingleLedger q SingleComp.xx).CorrectedLevel Lambda := by
  unfold SingleComp.nextSingleLedger
  split_ifs with hw
  · exact hL
  · simpa [SingleLedger.CorrectedLevel, SingleComp.next, SingleComp.cxInc,
      SingleComp.cyInc] using hL

/-- The `YY` event leaves the corrected doubled level unchanged. -/
theorem nextSingleLedger_correctedLevel_yy {n Lambda : ℕ}
    (q : SingleLedger n) (hL : q.CorrectedLevel Lambda) :
    (SingleComp.nextSingleLedger q SingleComp.yy).CorrectedLevel Lambda := by
  unfold SingleComp.nextSingleLedger
  split_ifs with hw
  · exact hL
  · simpa [SingleLedger.CorrectedLevel, SingleComp.next, SingleComp.cxInc,
      SingleComp.cyInc] using hL

/-- The `BB` event leaves the corrected doubled level unchanged. -/
theorem nextSingleLedger_correctedLevel_bb {n Lambda : ℕ}
    (q : SingleLedger n) (hL : q.CorrectedLevel Lambda) :
    (SingleComp.nextSingleLedger q SingleComp.bb).CorrectedLevel Lambda := by
  unfold SingleComp.nextSingleLedger
  split_ifs with hw
  · exact hL
  · simpa [SingleLedger.CorrectedLevel, SingleComp.next, SingleComp.cxInc,
      SingleComp.cyInc] using hL

/-- `X+Y → X+B` leaves `Lambda = 2x+b+CY-CX` unchanged. -/
theorem nextSingleLedger_correctedLevel_xyToX {n Lambda : ℕ}
    (q : SingleLedger n) (hL : q.CorrectedLevel Lambda) :
    (SingleComp.nextSingleLedger q SingleComp.xyToX).CorrectedLevel Lambda := by
  unfold SingleComp.nextSingleLedger
  split_ifs with hw
  · exact hL
  · rcases q with ⟨⟨⟨x, y, b⟩, hinv⟩, cx, cy, rx, ry⟩
    simp only [SingleLedger.CorrectedLevel, BiCfg.doubleLevel, SingleComp.next,
      SingleComp.cxInc, SingleComp.cyInc] at hL ⊢
    omega

/-- `X+Y → Y+B` leaves `Lambda = 2x+b+CY-CX` unchanged. -/
theorem nextSingleLedger_correctedLevel_xyToY {n Lambda : ℕ}
    (q : SingleLedger n) (hL : q.CorrectedLevel Lambda) :
    (SingleComp.nextSingleLedger q SingleComp.xyToY).CorrectedLevel Lambda := by
  unfold SingleComp.nextSingleLedger
  split_ifs with hw
  · exact hL
  · rcases q with ⟨⟨⟨x, y, b⟩, hinv⟩, cx, cy, rx, ry⟩
    simp only [SingleLedger.CorrectedLevel, BiCfg.doubleLevel, SingleComp.next,
      SingleComp.weight, SingleComp.cxInc, SingleComp.cyInc] at hL hw ⊢
    have hx0 : x ≠ 0 := fun hx => hw (by simp [hx])
    have hx : 1 ≤ x := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hx0)
    omega

/-- `X+B → 2X` raises the corrected doubled level by one. -/
theorem nextSingleLedger_correctedLevel_xb {n Lambda : ℕ}
    (q : SingleLedger n) (hL : q.CorrectedLevel Lambda)
    (hw : SingleComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b SingleComp.xb ≠ 0) :
    (SingleComp.nextSingleLedger q SingleComp.xb).CorrectedLevel (Lambda + 1) := by
  unfold SingleComp.nextSingleLedger
  rw [dif_neg hw]
  rcases q with ⟨⟨⟨x, y, b⟩, hinv⟩, cx, cy, rx, ry⟩
  simp only [SingleLedger.CorrectedLevel, BiCfg.doubleLevel, SingleComp.next,
    SingleComp.weight, SingleComp.cxInc, SingleComp.cyInc] at hL hw ⊢
  rw [Nat.mul_ne_zero_iff] at hw
  have hb : 1 ≤ b := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hw.2)
  omega

/-- `Y+B → 2Y` lowers the corrected doubled level by one, stated additively. -/
theorem nextSingleLedger_correctedLevel_yb {n Lambda : ℕ}
    (q : SingleLedger n) (hL : q.CorrectedLevel (Lambda + 1))
    (hw : SingleComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b SingleComp.yb ≠ 0) :
    (SingleComp.nextSingleLedger q SingleComp.yb).CorrectedLevel Lambda := by
  unfold SingleComp.nextSingleLedger
  rw [dif_neg hw]
  rcases q with ⟨⟨⟨x, y, b⟩, hinv⟩, cx, cy, rx, ry⟩
  simp only [SingleLedger.CorrectedLevel, BiCfg.doubleLevel, SingleComp.next,
    SingleComp.weight, SingleComp.cxInc, SingleComp.cyInc] at hL hw ⊢
  rw [Nat.mul_ne_zero_iff] at hw
  have hb : 1 ≤ b := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hw.2)
  omega

end SingleComp

section Inhabitation

example :
    let q : SingleLedger 5 :=
      { cfg := ⟨⟨3, 1, 1⟩, by norm_num [BiCfg.DoubleInv]⟩
        cx := 2
        cy := 3
        rx := 0
        ry := 0 }
    3 + q.cfg.1.y ≤ q.cfg.1.x + 1 := by
  intro q
  exact single_gap_recover (G := 3) (D := 1) q (by norm_num) (by norm_num)

example :
    let q : SingleLedger 5 :=
      { cfg := ⟨⟨5, 0, 0⟩, by norm_num [BiCfg.DoubleInv]⟩
        cx := 1
        cy := 3
        rx := 0
        ry := 0 }
    BiXConsensus 5 q.cfg.1 := by
  intro q
  exact single_consensus_export (D := 2) q (by norm_num) (by norm_num)

end Inhabitation

end Tri

#print axioms Tri.singleLedger_corrected_gap
#print axioms Tri.single_gap_recover
#print axioms Tri.single_co_recover
#print axioms Tri.single_consensus_export
#print axioms Tri.SingleComp.nextSingleLedger_correctedLevel_xx
#print axioms Tri.SingleComp.nextSingleLedger_correctedLevel_yy
#print axioms Tri.SingleComp.nextSingleLedger_correctedLevel_bb
#print axioms Tri.SingleComp.nextSingleLedger_correctedLevel_xyToX
#print axioms Tri.SingleComp.nextSingleLedger_correctedLevel_xyToY
#print axioms Tri.SingleComp.nextSingleLedger_correctedLevel_xb
#print axioms Tri.SingleComp.nextSingleLedger_correctedLevel_yb
