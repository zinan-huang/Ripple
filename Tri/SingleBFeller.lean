/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBProductiveTail

/-!
# Single-B physical return producer

`singleBand_phase_reaches` asks for a return bound on the physical event
`x <= returnLo`.  The current Single-B corrected-level martingale does not by
itself imply that physical event after the ledger is forgotten.  This file
therefore exports a conservative producer for the exact `hruin` shape: when
the displayed return ratio is at least one, the bound follows from total mass.
-/

namespace Tri

open scoped ENNReal

/-- Any Single-B hitting probability is at most one. -/
theorem singleB_hitProb_le_one {n : Nat} (hn : 2 <= n)
    (returnLo U : Nat) (s : SingleState n) :
    hitProb (fun z : SingleState n => z.1.x <= returnLo)
      (singleStateStep n hn) U s <= 1 := by
  unfold hitProb expect ind
  calc
    (∑' z, iter (freeze (fun z : SingleState n => z.1.x <= returnLo)
          (singleStateStep n hn)) U s z *
        if (fun z : SingleState n => z.1.x <= returnLo) z then 1 else 0)
      <= ∑' z, iter (freeze (fun z : SingleState n => z.1.x <= returnLo)
          (singleStateStep n hn)) U s z := by
        exact ENNReal.tsum_le_tsum fun z => by
          by_cases hz : z.1.x <= returnLo <;> simp [hz]
    _ = 1 := PMF.tsum_coe _

/-- If the displayed return ratio is at least one, the exact physical return
bound requested by the staged Single-B theorem follows from total mass. -/
theorem singleB_return_trivial {n : Nat} (hn : 2 <= n)
    (returnLo bHiRet kRet U : Nat)
    (hreturnLo : 0 < returnLo) (hle : returnLo <= bHiRet)
    (s : SingleState n) :
    hitProb (fun z : SingleState n => z.1.x <= returnLo)
      (singleStateStep n hn) U s
      <= ((bHiRet : ENNReal) / (returnLo : ENNReal)) ^ kRet := by
  have hret0 : (returnLo : ENNReal) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hretT : (returnLo : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hbase : 1 <= (bHiRet : ENNReal) / (returnLo : ENNReal) := by
    calc
      (1 : ENNReal) = (returnLo : ENNReal) / (returnLo : ENNReal) :=
        (ENNReal.div_self hret0 hretT).symm
      _ <= (bHiRet : ENNReal) / (returnLo : ENNReal) :=
        ENNReal.div_le_div_right (by exact_mod_cast hle) _
  exact (singleB_hitProb_le_one hn returnLo U s).trans (one_le_pow₀ hbase)

/-- A producer for the `hruin` hypothesis of `singleBand_phase_reaches`. -/
theorem singleBand_hruin_trivial {n : Nat} (hn : 2 <= n)
    (aLoΛ hiΛ D H returnLo bHiRet kRet : Nat)
    (hreturnLo : 0 < returnLo) (hle : returnLo <= bHiRet)
    (Exit : SingleState n -> Prop) [DecidablePred Exit] :
    forall q : SingleLedger n,
      SingleBandFrozen n aLoΛ hiΛ D H q -> Exit q.cfg -> forall U : Nat,
        hitProb (fun z : SingleState n => z.1.x <= returnLo)
          (singleStateStep n hn) U q.cfg
          <= ((bHiRet : ENNReal) / (returnLo : ENNReal)) ^ kRet := by
  intro q _hB _hExit U
  exact singleB_return_trivial hn returnLo bHiRet kRet U hreturnLo hle q.cfg

end Tri

#print axioms Tri.singleB_hitProb_le_one
#print axioms Tri.singleB_return_trivial
#print axioms Tri.singleBand_hruin_trivial
